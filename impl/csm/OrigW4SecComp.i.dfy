module Impl.Csm.OrigW4SecComp {
  import opened Constants
  import opened Types
  import opened External.Logging

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened L2cCsmExtern.Helpers
  import opened Utils

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_orig_w4_sec_comp(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_ORIG_W4_SEC_COMP)
             && p_ccb.p_lcb_o != null
    // functionality specifications
    modifies p_ccb`chnl_state,
             p_ccb`p_lcb_o
    modifies p_ccb.p_lcb_o
    requires match event {
               case
                 | L2CEVT_L2CAP_DATA
                 | L2CEVT_L2CA_DATA_WRITE => true
               case _ => false
             }
             ==> p_data.View?
    // state machine specifications
    requires !csm.IsDestroyedState()
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
  {
    log_csm_execution_start_prefix(
      "OrigW4SecComp",
      (if p_ccb.p_lcb_o.is_ble() then "LE " else "") + " - ",
      CST_ORIG_W4_SEC_COMP,
      event,
      p_ccb
    );

    csm.Execute(OpsEvent(event, p_ccb));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        log_disconnect_ind("OrigW4SecComp", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_SEC_RE_SEND_CMD /* BTM has enough info to proceed */
        | L2CEVT_LP_CONNECT_CFM /* Link came up         */ =>
        if (p_ccb.p_lcb_o.is_ble()) {
          // NOTE: in C++ code, is_originator parameter is set to false
          var _ := l2ble_sec_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(), p_ccb.rcb_psm(),
                                        true, p_ccb.GetExternalHandle());
        } else {
          var _ := btm_sec_l2cap_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(),
                                            p_ccb.rcb_psm(), true, p_ccb.GetExternalHandle());
        }

      case L2CEVT_SEC_COMP /* Security completed success */ =>
        /* Wait for the info resp in this state before sending connect req (if
         * needed) */
        p_ccb.chnl_state := CST_W4_L2CAP_CONNECT_RSP;
        if (p_ccb.p_lcb_o.is_ble()) {
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);
          l2cble_credit_based_conn_req(csm, p_ccb.GetExternalHandle()); /* Start Connection     */
        } else {
          if !p_ccb.p_lcb_o.w4_info_rsp() {
            /* Need to have at least one compatible channel to continue */
            var res := l2c_fcr_chk_chan_modes(p_ccb.GetExternalHandle());
            if (!res) {
              l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
              p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);
            } else {
              alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);
              l2cu_send_peer_connect_req(csm, p_ccb.GetExternalHandle()); /* Start Connection     */
            }
          }
        }

      case L2CEVT_SEC_COMP_NEG =>
        /* If last channel immediately disconnect the ACL for better security.
          Also prevents a race condition between BTM and L2CAP */
        p_ccb.remove_timeout_if_only_channel();

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */
        | L2CEVT_L2CAP_DATA     /* Peer data packet rcvd    */ =>
        l2c_csm_osi_free(p_data.view);

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper wants to disconnect */
        /* Tell security manager to abort */ =>
        btm_sec_abort_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr());

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case _ =>
        log("OrigW4SecComp", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("OrigW4SecComp", p_ccb.chnl_state, event);
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB): OsmEvent
    requires p_ccb.p_lcb_o != null
    reads p_ccb,
          p_ccb.p_lcb_o
  {
    var mode := l2c_csm_connection_mode(p_ccb);
    var should_wait_info_rsp := p_ccb.p_lcb_o.w4_info_rsp();
    match event {
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_LP_CONNECT_CFM | L2CEVT_SEC_RE_SEND_CMD
        => Local(SecurityCheckComplete(Resend))
      case L2CEVT_SEC_COMP =>
        if (mode != Classic) then Local(SecurityCheckComplete(CheckResult.Success(should_wait_info_rsp, mode)))
        else
        if !should_wait_info_rsp then
          if l2c_csm_incompatible_channels(p_ccb) then Local(SecurityCheckComplete(CheckResult.Failure))
          else Local(SecurityCheckComplete(CheckResult.Success(false, Classic)))
        else Local(SecurityCheckComplete(CheckResult.Success(true, Classic)))
      case L2CEVT_SEC_COMP_NEG => Local(SecurityCheckComplete(CheckResult.Failure))
      case L2CEVT_L2CAP_DATA => Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE => Local(WriteData)
      case L2CEVT_L2CA_DISCONNECT_REQ => Local(LocalEvent.DisconnectReq)
      case _ => Unmodeled
    }
  }
}
