module Impl.Csm.Closed {
  import opened Constants
  import opened Types
  import opened Utils
  import opened CommonTypes
  import opened External.Logging

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened L2cCsmExtern.Helpers
  import opened TermW4SecComp

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_closed(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT , p_ci: DataPossibleView<ConnectionInfo>, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_CLOSED)
    requires p_ccb.external_event.None?
    requires p_ccb.p_lcb_o != null

    // functionality specifications
    requires p_ccb.fcr_cfg_tries > 0
    modifies p_ccb`chnl_state,
             p_ccb`p_lcb_o,
             // Config related
             p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result,
             {}
    modifies p_ccb`external_event, p_ccb`destroy_handle
    modifies p_ccb.p_lcb_o
    modifies p_ccb`flags
    ensures match event {
              case
                | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ
                | L2CEVT_L2CAP_CONNECT_REQ  => false
              case _ => true
            }
            ==> unchanged(p_ccb`flags)
    requires (event in
                {
                  L2CEVT_LP_CONNECT_CFM_NEG
                }
             ) ==> p_ci.View?
    requires match event {
               case
                 | L2CEVT_L2CAP_DATA
                 | L2CEVT_L2CA_DATA_WRITE => true
               case _ => false
             }
             ==> p_data.View?
    // state machine specifications
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
    decreases RecursiveCount(event)
  {
    log_csm_execution_start("Closed", CST_CLOSED, event, p_ccb);

    csm.Execute(OpsEvent(event, p_ccb));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND =>
        log_disconnect_ind("Closed", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_LP_CONNECT_CFM =>
        if (p_ccb.p_lcb_o.is_ble()) {
          p_ccb.chnl_state := CST_ORIG_W4_SEC_COMP;
          var res := l2ble_sec_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(), p_ccb.rcb_psm(),
                                          true, p_ccb.GetExternalHandle());
        } else {
          p_ccb.chnl_state := CST_ORIG_W4_SEC_COMP;
          var res := btm_sec_l2cap_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(),
                                              p_ccb.rcb_psm(), true, p_ccb.GetExternalHandle());
        }

      case L2CEVT_LP_CONNECT_CFM_NEG =>
        var p_ci := p_ci.view;
        if (p_ci.status() == HCI_ERR_CONNECTION_EXISTS) {
          btm_acl_notif_conn_collision(p_ccb.p_lcb_o.remote_bd_addr());
          // FIXME: Model
          assume p_ccb.IsDestroyed();
        } else {
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
          p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);
        }

      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ | L2CEVT_L2CA_CONNECT_REQ =>
        // NOTE: state transition to CST_ORIG_W4_SEC_COMP is modelled through the L2CEVT_SEC_ACCESS_PND event
        if (p_ccb.p_lcb_o.is_ble()) {
          p_ccb.chnl_state := CST_ORIG_W4_SEC_COMP;
          var res := l2ble_sec_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(), p_ccb.rcb_psm(),
                                          true, p_ccb.GetExternalHandle());
        } else {
          var success := BTM_SetLinkPolicyActiveMode(p_ccb.p_lcb_o.remote_bd_addr());
          if (!success) {
            log("Closed", Warn, "Unable to set link policy active");
          }
          /* If sec access does not result in started SEC_COM or COMP_NEG are
           * already processed */
          var res := btm_sec_l2cap_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(),
                                              p_ccb.rcb_psm(), true, p_ccb.GetExternalHandle());
          if (res == BTM_CMD_STARTED) {
            l2c_csm_closed(csm, p_ccb, L2CEVT_SEC_ACCESS_PND, p_ci, p_data); // p_ccb.chnl_state := CST_ORIG_W4_SEC_COMP;
          }
        }

      case L2CEVT_SEC_ACCESS_PND =>
        p_ccb.chnl_state := CST_ORIG_W4_SEC_COMP;

      case L2CEVT_SEC_COMP =>
        p_ccb.chnl_state := CST_W4_L2CAP_CONNECT_RSP;

        if (!p_ccb.p_lcb_o.w4_info_rsp()) {
          /* Need to have at least one compatible channel to continue */
          var res := l2c_fcr_chk_chan_modes(p_ccb.GetExternalHandle());
          if (!res) {
            l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
            p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);
          } else {
            l2cu_send_peer_connect_req(csm, p_ccb.GetExternalHandle());
            // TODO: model alarm actions
            alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);
          }
        }

      case L2CEVT_SEC_COMP_NEG =>
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);

      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ | L2CEVT_L2CAP_CONNECT_REQ =>
        /* stop link timer to avoid race condition between A2MP, Security, and
         * L2CAP */
        // TODO: model alarm actions
        alarm_cancel_lcb(p_ccb.p_lcb_o.GetExternalHandle());
        var result: uint8_t;
        var is_ble: bool := p_ccb.p_lcb_o.is_ble();

        if (is_ble) {
          p_ccb.chnl_state := CST_TERM_W4_SEC_COMP;
          result := l2ble_sec_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(), p_ccb.rcb_psm(),
                                         false, p_ccb.GetExternalHandle());
          // if (result == L2CAP_LE_RESULT_INSUFFICIENT_AUTHORIZATION
          //     || result == L2CAP_LE_RESULT_UNACCEPTABLE_PARAMETERS
          //     || result == L2CAP_LE_RESULT_INVALID_PARAMETERS
          //     || result == L2CAP_LE_RESULT_INSUFFICIENT_AUTHENTICATION
          //     || result == L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP_KEY_SIZE
          //     || result == L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP)
          // {
          //   l2cu_reject_ble_connection(csm, p_ccb, p_ccb.remote_id, result);
          //   l2cu_release_ccb(csm, p_ccb);
          // }
        } else {
          var success := BTM_SetLinkPolicyActiveMode(p_ccb.p_lcb_o.remote_bd_addr());
          if (!success) {
            log("Closed", Warn, "Unable to set link policy active");
          }
          p_ccb.chnl_state := CST_TERM_W4_SEC_COMP;
          result := btm_sec_l2cap_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(),
                                             p_ccb.rcb_psm(), false, p_ccb.GetExternalHandle());
          // if (result == BTM_CMD_STARTED) {
          //   // started the security process, tell the peer to set a longer timer
          //   l2cu_send_peer_connect_rsp(csm, p_ccb, L2CAP_CONN_PENDING, 0);
          // } else {
          // log(Info, fmt_uint16("Check security for psm 0x%04x", p_ccb.rcb_psm()) + fmt_uint8(", status %d", result));
          // }
        }
        l2c_csm_term_w4_sec_comp(csm, p_ccb, model_sec_access_res(is_ble, result), DataPossibleView.Unavailable, Some(result), DataPossibleView.Unavailable);

      case L2CEVT_TIMEOUT =>
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);

      case L2CEVT_L2CAP_DATA | L2CEVT_L2CA_DATA_WRITE =>
        l2c_csm_osi_free(p_data.view);

      case L2CEVT_L2CA_DISCONNECT_REQ =>
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case _ =>
        log("Closed", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("Closed", p_ccb.chnl_state, event);
  }

  function model_sec_access_res(is_ble: bool, result: uint8_t): tL2CEVT {
    if is_ble then
      if (result == L2CAP_LE_RESULT_INSUFFICIENT_AUTHORIZATION
          || result == L2CAP_LE_RESULT_UNACCEPTABLE_PARAMETERS
          || result == L2CAP_LE_RESULT_INVALID_PARAMETERS
          || result == L2CAP_LE_RESULT_INSUFFICIENT_AUTHENTICATION
          || result == L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP_KEY_SIZE
          || result == L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP)
      then L2CEVT_SEC_ACCESS_NEG
      else L2CEVT_SEC_ACCESS
    else if (result == BTM_CMD_STARTED) then L2CEVT_SEC_ACCESS_PND
    else L2CEVT_SEC_ACCESS
  }

  ghost function RecursiveCount(event: tL2CEVT): int {
    if event == L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ || event == L2CEVT_L2CA_CONNECT_REQ then
      1
    else 0
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB): OsmEvent
    requires p_ccb.p_lcb_o != null
    reads p_ccb,
          p_ccb.p_lcb_o
  {
    var mode := l2c_csm_connection_mode(p_ccb);
    match event {
      case L2CEVT_LP_DISCONNECT_IND | L2CEVT_LP_CONNECT_CFM_NEG => Local(LinkDisconnectInd)
      case L2CEVT_LP_CONNECT_CFM
        => Local(OpenChannelReq)
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ | L2CEVT_L2CA_CONNECT_REQ
        => if p_ccb.p_lcb_o.is_ble() then Local(OpenChannelReq)
      else Local(SecurityCheckComplete(Resend))
      case L2CEVT_SEC_ACCESS_PND => Local(SecurityCheckComplete(CheckResult.Pending))
      case L2CEVT_SEC_COMP =>
        if (p_ccb.p_lcb_o.w4_info_rsp()) then Local(SecurityCheckComplete(CheckResult.Success(true, mode)))
        else if l2c_csm_incompatible_channels(p_ccb) then Local(SecurityCheckComplete(CheckResult.Failure))
        else Local(SecurityCheckComplete(CheckResult.Success(false, mode)))
      case L2CEVT_SEC_COMP_NEG
        => Local(SecurityCheckComplete(CheckResult.Failure))
      case L2CEVT_TIMEOUT => Local(Timeout)
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ | L2CEVT_L2CAP_CONNECT_REQ
        => Packet(ConnectReq)
      case L2CEVT_L2CAP_DATA => Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE => Local(WriteData)
      case L2CEVT_L2CA_DISCONNECT_REQ => Local(LocalEvent.DisconnectReq)
      // by default ignore other events
      case _ => Unmodeled
    }
  }
}
