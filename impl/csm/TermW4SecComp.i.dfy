module Impl.Csm.TermW4SecComp {
  import opened CommonTypes
  import opened Constants
  import opened Types
  import opened Utils
  import opened External.Logging

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened L2cCsmExtern.Helpers
  import opened W4L2caConnectRsp
  import opened Config

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_term_w4_sec_comp(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT , p_ci: DataPossibleView<ConnectionInfo>, p_ci_status: Option<uint8_t>, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_TERM_W4_SEC_COMP)
             && p_ccb.p_lcb_o != null
    modifies p_ccb`chnl_state,
             p_ccb`external_event, p_ccb`destroy_handle,
             p_ccb`p_lcb_o
    modifies
      // Config related
      p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result,
             {}
    modifies p_ccb.p_lcb_o
    modifies p_ccb`flags
    ensures match event {
              case
                | L2CEVT_SEC_COMP
                | L2CEVT_SEC_COMP_NEG
                | L2CEVT_SEC_ACCESS_PND => false
              case _ => true
            }
            ==> unchanged(p_ccb`flags)
    requires (event in
                {
                  L2CEVT_SEC_ACCESS,
                  L2CEVT_SEC_COMP_NEG,
                  L2CEVT_SEC_ACCESS_NEG
                }
             ) ==> (p_ci.View? || p_ci_status.Some?)
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
  {
    log_csm_execution_start("TermW4SecComp", CST_TERM_W4_SEC_COMP, event, p_ccb);

    var conn_info_status := if p_ci_status.Some? then p_ci_status else if p_ci.View? then Some(p_ci.view.status()) else None;
    csm.Execute(OpsEvent(event, p_ccb, conn_info_status));

    /**
      * The first 3 events (i.e. L2CEVT_SEC_ACCESS*) are to handle security access check results from previous execution.
      */
    match (event) {
      case L2CEVT_SEC_ACCESS =>
        log("TermW4SecComp", Info, "Check security for psm " + fmt_uint16("0x%04x", p_ccb.rcb_psm()) + ", status " + fmt_uint8("%d", conn_info_status.value));

      case L2CEVT_SEC_ACCESS_PND =>
        if (!p_ccb.p_lcb_o.is_ble()) {
          l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_PENDING, 0);
        }

      case L2CEVT_SEC_ACCESS_NEG =>
        if (p_ccb.p_lcb_o.is_ble()) {
          l2cu_reject_ble_connection(csm, p_ccb.GetExternalHandle(), p_ccb.remote_id(), conn_info_status.value);
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        }

      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        /* Tell security manager to abort */
        btm_sec_abort_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr());

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_SEC_COMP =>
        p_ccb.chnl_state := CST_W4_L2CA_CONNECT_RSP;

        /* Wait for the info resp in next state before sending connect ind (if
         * needed) */
        if (!p_ccb.p_lcb_o.w4_info_rsp()) {
          log("TermW4SecComp", Debug, "Not waiting for info response, sending connect response");
          /* Don't need to get info from peer or already retrieved so continue */
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);

          if (!p_ccb.p_lcb_o.is_ble()) {
            log("TermW4SecComp", Debug, "Not LE connection, sending configure request");
            l2c_csm_w4_l2ca_connect_rsp(csm, p_ccb, L2CEVT_L2CA_CONNECT_RSP, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2c_csm_send_connect_rsp(p_ccb);
            var cfg := l2c_csm_send_config_req_set_and_get_our_cfg(p_ccb.GetExternalHandle());
            l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_REQ, DataPossibleView.View(cfg), DataPossibleView.Unavailable, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2c_csm_send_config_req(p_ccb);
          } else {
            if (p_ccb.ecoc()) {
              // assert csm.model.state == AcceptorWaitSecurityCheck;
              // assert OpsEvent(L2CEVT_SEC_COMP, p_ccb, p_data) == Unmodeled;
              l2c_csm_indicate_credit_based_connection_open(p_ccb.GetExternalHandle());
            } else {
              /* Handle BLE CoC */
              log("TermW4SecComp", Debug, "Calling Connect_Ind_Cb(), " + fmt_cid(p_ccb));
              l2c_csm_w4_l2ca_connect_rsp(csm, p_ccb, L2CEVT_L2CA_CONNECT_RSP, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2c_csm_send_connect_rsp(p_ccb);
              l2c_csm_indicate_connection_open(p_ccb.GetExternalHandle());
            }
          }
        } else {
          /*
           ** L2CAP Connect Response will be sent out by 3 sec timer expiration
           ** because Bluesoleil doesn't respond to L2CAP Information Request.
           ** Bluesoleil seems to disconnect ACL link as failure case, because
           ** it takes too long (4~7secs) to get response.
           ** product version : Bluesoleil 2.1.1.0 EDR Release 060123
           ** stack version   : 05.04.11.20060119
           */

          /* Waiting for the info resp, tell the peer to set a longer timer */
          log("TermW4SecComp", Debug, "Waiting for info response, sending connect pending");
          l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_PENDING, 0);
        }

      case L2CEVT_SEC_COMP_NEG =>
        var p_ci_status := conn_info_status.value;
        if (p_ci_status == BTM_DELAY_CHECK) {
          /* start a timer - encryption change not received before L2CAP connect
           * req */
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_DELAY_CHECK_SM4_TIMEOUT_MS);
        } else {
          if (p_ccb.p_lcb_o.is_ble()) {
            l2cu_reject_ble_connection(csm, p_ccb.GetExternalHandle(), p_ccb.remote_id(), p_ci_status);
          } else {
            l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_SECURITY_BLOCK, 0);
          }
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        }

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */
        | L2CEVT_L2CAP_DATA     /* Peer data packet rcvd    */ =>
        l2c_csm_osi_free(p_data.view);

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper wants to disconnect */ =>
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_L2CAP_DISCONNECT_REQ /* Peer disconnected request */ =>
        l2cu_send_peer_disc_rsp(csm, p_ccb.p_lcb_o.GetExternalHandle(), p_ccb.remote_id(), p_ccb.local_cid(), p_ccb.remote_cid);

        /* Tell security manager to abort */
        btm_sec_abort_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr());

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_TIMEOUT /* SM4 related. */ =>
        acl_disconnect_from_handle(p_ccb.GetExternalHandle(), HCI_ERR_AUTH_FAILURE);

      case L2CEVT_SEC_RE_SEND_CMD /* BTM has enough info to proceed */ =>
        var res := btm_sec_l2cap_access_req(csm, p_ccb.p_lcb_o.remote_bd_addr(), p_ccb.rcb_psm(), false, p_ccb.GetExternalHandle());

      case _ =>
        log("TermW4SecComp", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("TermW4SecComp", p_ccb.chnl_state, event);
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB, status: Option<uint8_t>): OsmEvent
    requires p_ccb.p_lcb_o != null
    requires event == L2CEVT_SEC_COMP_NEG ==> status.Some?
    reads {},
          p_ccb,
          p_ccb.p_lcb_o,
          {}
  {
    var mode := l2c_csm_connection_mode(p_ccb);
    match event {
      case L2CEVT_SEC_ACCESS => Unmodeled
      case L2CEVT_TIMEOUT => Local(Timeout)
      case L2CEVT_SEC_ACCESS_PND =>
        if !p_ccb.p_lcb_o.is_ble()
        then Local(SecurityCheckComplete(CheckResult.Pending))
        else Unmodeled
      case L2CEVT_SEC_ACCESS_NEG =>
        if p_ccb.p_lcb_o.is_ble()
        then Local(SecurityCheckComplete(CheckResult.Failure))
        else Unmodeled
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_SEC_COMP =>
        Local(SecurityCheckComplete(
                if !p_ccb.p_lcb_o.w4_info_rsp() then
                  if mode == Ble && p_ccb.ecoc() then CheckResult.Success(false, CreditBased)
                  else CheckResult.Success(false, mode)
                else CheckResult.Success(true, mode)
              ))
      case L2CEVT_SEC_COMP_NEG =>
        if status.value == BTM_DELAY_CHECK then Unmodeled
        else Local(SecurityCheckComplete(CheckResult.Failure))
      case L2CEVT_L2CAP_DATA => Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE => Local(WriteData)
      case L2CEVT_L2CA_DISCONNECT_REQ => Local(LocalEvent.DisconnectReq)
      case L2CEVT_L2CAP_DISCONNECT_REQ => Packet(PacketEvent.DisconnectReq)
      case L2CEVT_SEC_RE_SEND_CMD => Local(SecurityCheckComplete(CheckResult.Resend))
      // by default ignore all other events
      case _ => Unmodeled
    }
  }
}
