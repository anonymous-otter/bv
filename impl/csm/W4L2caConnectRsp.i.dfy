module Impl.Csm.W4L2caConnectRsp {
  import opened Constants
  import opened Types
  import opened Utils
  import opened External.Logging

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened L2cCsmExtern.Helpers
  import opened Config

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_w4_l2ca_connect_rsp(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT, p_ci: DataPossibleView<ConnectionInfo>, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_W4_L2CA_CONNECT_RSP)
    // functionality specifications
    requires match event {
               case
                 | L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP
                 | L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG
                 | L2CEVT_L2CA_CONNECT_RSP
                 | L2CEVT_L2CA_CONNECT_RSP_NEG
                 | L2CEVT_L2CAP_INFO_RSP
                 | L2CEVT_L2CA_DISCONNECT_REQ
                 | L2CEVT_TIMEOUT => true
               case _ => false
             }
             ==> p_ccb.p_lcb_o != null
    modifies p_ccb`chnl_state,
             p_ccb`p_lcb_o,
             p_ccb`external_event, p_ccb`destroy_handle,
             // Config related
             p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result,
             {}

    requires (event in
                {
                  L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP,
                  L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG,
                  L2CEVT_L2CA_CONNECT_RSP_NEG
                }
             ) ==> p_ci.View?
    requires match event {
               case
                 | L2CEVT_L2CAP_DATA
                 | L2CEVT_L2CA_DATA_WRITE => true
               case _ => false
             }
             ==> p_data.View?

    requires match event {
               case L2CEVT_L2CA_CONNECT_RSP =>
                 && p_ci.View? && p_ci.view.l2cap_result() != L2CAP_CONN_OK
                 ==> p_ci.view.l2cap_result() == L2CAP_CONN_PENDING
               case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP =>
                 p_ci.view.l2cap_result() == L2CAP_CONN_OK
               case L2CEVT_L2CA_CONNECT_RSP_NEG =>
                 p_ci.view.l2cap_result() != L2CAP_CONN_OK && p_ci.view.l2cap_result() != L2CAP_CONN_PENDING
               case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG =>
                 p_ci.view.l2cap_result() != L2CAP_CONN_OK
               case _ => true
             }
    requires (event == L2CEVT_L2CAP_INFO_RSP && p_ccb.p_lcb_o.is_ble()) ==> p_ccb.fcr_cfg_tries > 0
    modifies p_ccb`external_event
    modifies p_ccb.p_lcb_o
    modifies p_ccb`flags
    ensures match event {
              case
                | L2CEVT_L2CA_CONNECT_RSP
                | L2CEVT_L2CA_CONNECT_RSP_NEG
                | L2CEVT_TIMEOUT
                | L2CEVT_L2CAP_INFO_RSP => false
              case _ => true
            }
            ==> unchanged(p_ccb`flags)
    // state machine specifications
    requires p_ccb.external_event.None?
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
    ensures event == L2CEVT_L2CA_CONNECT_RSP && !old(p_ccb.p_lcb_o).is_ble() && p_ci.Unavailable? ==>
              && p_ccb.chnl_state == CST_CONFIG && !p_ccb.IsDestroyed()
              && p_ccb.p_lcb_o == old(p_ccb.p_lcb_o)
  {
    log_csm_execution_start("W4L2caConnectRsp", CST_W4_L2CA_CONNECT_RSP, event, p_ccb);

    csm.Execute(OpsEvent(event, p_ccb, p_ci));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        log_disconnect_ind("W4L2caConnectRsp", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP =>
        var p_ci := p_ci.view;
        if (p_ccb.p_lcb_o != null && !p_ccb.p_lcb_o.is_ble()) {
          log("W4L2caConnectRsp", Warn, "LE link doesn't exist");
          return;
        }
        l2cu_send_peer_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), p_ci.GetExternalHandle());

        alarm_cancel(p_ccb.GetExternalHandle());

        // for (int i = 0; i < p_ccb->p_lcb->pending_ecoc_conn_cnt; i++) {
        //   uint16_t cid = p_ccb->p_lcb->pending_ecoc_connection_cids[i];
        //   tL2C_CCB* temp_p_ccb = l2cu_find_ccb_by_cid(p_ccb->p_lcb, cid);
        //   auto it = std::find(p_ci->lcids.begin(), p_ci->lcids.end(), cid);
        //   if (it != p_ci->lcids.end()) {
        //     temp_p_ccb->chnl_state = CST_OPEN;
        //   } else {
        //     l2cu_release_ccb(temp_p_ccb);
        //   }
        // }
        // p_ccb->p_lcb->pending_ecoc_conn_cnt = 0;
        // memset(p_ccb->p_lcb->pending_ecoc_connection_cids, 0,
        //       L2CAP_CREDIT_BASED_MAX_CIDS);

        // NOTE: the above logic will be modeled as a separate function.
        l2c_csm_open_credit_based_conn(p_ccb.GetExternalHandle(), p_ci.GetExternalHandle());

      case L2CEVT_L2CA_CONNECT_RSP =>
        if (p_ccb.p_lcb_o.is_ble()) {
          /* Result should be OK or Reject */
          if (p_ci.Unavailable? || p_ci.view.l2cap_result() == L2CAP_CONN_OK) {
            l2cble_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_OK);
            p_ccb.chnl_state := CST_OPEN;
            alarm_cancel(p_ccb.GetExternalHandle());
          } else {
            l2cble_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), p_ci.view.l2cap_result());
            l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
          }
        } else {
          /* Result should be OK or PENDING */
          if (p_ci.Unavailable? || p_ci.view.l2cap_result() == L2CAP_CONN_OK) {
            log("W4L2caConnectRsp", Debug, "Sending connection ok for BR_EDR");
            l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_OK, 0);
            p_ccb.chnl_state := CST_CONFIG;
            alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);
          } else {
            var p_ci := p_ci.view;
            /* If pending, stay in same state and start extended timer */
            log("W4L2caConnectRsp", Debug, "Sending connection result " + fmt_uint16("%d", p_ci.l2cap_result()) +" and status " + fmt_uint8("%d", p_ci.status()));
            l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), p_ci.l2cap_result(), p_ci.l2cap_status());
            alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_EXT_TIMEOUT_MS);
          }
        }

      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG =>
        var p_ci := p_ci.view;
        if (p_ccb.p_lcb_o != null && p_ccb.p_lcb_o.is_ble()) {
          l2cu_send_peer_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), p_ci.GetExternalHandle());
        }
        alarm_cancel(p_ccb.GetExternalHandle());
        // for (int i = 0; i < p_ccb->p_lcb->pending_ecoc_conn_cnt; i++) {
        //   uint16_t cid = p_ccb->p_lcb->pending_ecoc_connection_cids[i];
        //   tL2C_CCB* temp_p_ccb = l2cu_find_ccb_by_cid(p_ccb->p_lcb, cid);
        //   l2cu_release_ccb(temp_p_ccb);
        // }

        // p_ccb->p_lcb->pending_ecoc_conn_cnt = 0;
        // memset(p_ccb->p_lcb->pending_ecoc_connection_cids, 0,
        //       L2CAP_CREDIT_BASED_MAX_CIDS);

        // NOTE: the above logic will be modeled as a separate function.
        l2c_csm_close_credit_based_conn(csm, p_ccb.GetExternalHandle(), true);

      case L2CEVT_L2CA_CONNECT_RSP_NEG =>
        var p_ci := p_ci.view;
        if (p_ccb.p_lcb_o.is_ble()) {
          l2cble_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), p_ci.l2cap_result());
        } else {
          l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), p_ci.l2cap_result(), p_ci.l2cap_status());
        }
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_TIMEOUT =>
        l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_NO_PSM, 0);
        log_disconnect_ind("W4L2caConnectRsp", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */
        | L2CEVT_L2CAP_DATA      /* Peer data packet rcvd */ =>
        l2c_csm_osi_free(p_data.view);

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper wants to disconnect */ =>
        l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
        p_ccb.chnl_state := CST_W4_L2CAP_DISCONNECT_RSP;
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);

      case L2CEVT_L2CAP_INFO_RSP =>
        /* We have feature info, so now give the upper layer connect IND */
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);
        log("W4L2caConnectRsp", Debug, "Calling Connect_Ind_Cb(), " + fmt_cid(p_ccb));

        // l2c_csm_send_connect_rsp(p_ccb);
        if (p_ccb.p_lcb_o.is_ble()) {
          l2cble_credit_based_conn_res(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_OK);
          p_ccb.chnl_state := CST_OPEN;
          alarm_cancel(p_ccb.GetExternalHandle());
        } else {
          log("W4L2caConnectRsp", Debug, "Sending connection ok for BR_EDR");
          l2cu_send_peer_connect_rsp(csm, p_ccb.GetExternalHandle(), L2CAP_CONN_OK, 0);
          p_ccb.chnl_state := CST_CONFIG;
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);
        }

        // l2c_csm_send_config_req(p_ccb);
        if (p_ccb.chnl_state == CST_CONFIG) {
          var cfg := l2c_csm_send_config_req_set_and_get_our_cfg(p_ccb.GetExternalHandle());
          l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_REQ, DataPossibleView.View(cfg), DataPossibleView.Unavailable, DataPossibleView.Unavailable, DataPossibleView.Unavailable);
        }

      case _ =>
        log("W4L2caConnectRsp", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("W4L2caConnectRsp", p_ccb.chnl_state, event);
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB, p_data: DataPossibleView<tL2C_CONN_INFO>): OsmEvent
    reads p_ccb, p_ccb.p_lcb_o,
          if event == L2CEVT_L2CA_CONNECT_RSP && p_data.View? then {p_data.view} else {},
          {}
    requires event == L2CEVT_L2CA_CONNECT_RSP || event == L2CEVT_L2CA_CONNECT_RSP_NEG
             ==> p_ccb.p_lcb_o != null
  {
    match event {
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP =>
        if p_ccb.p_lcb_o != null && !p_ccb.p_lcb_o.is_ble()
        then Unmodeled
        else Local(OpenChannelRsp(ConnectRspResult.Success, CreditBased))
      case L2CEVT_L2CA_CONNECT_RSP =>
        if p_data.Unavailable? || p_data.view.l2cap_result() == L2CAP_CONN_OK
        then Local(LocalEvent.OpenChannelRsp(ConnectRspResult.Success, l2c_csm_connection_mode(p_ccb)))
        else
          if p_ccb.p_lcb_o.is_ble() ||  p_data.view.l2cap_result() != L2CAP_CONN_PENDING
          then Local(LocalEvent.OpenChannelRsp(ConnectRspResult.Refused, l2c_csm_connection_mode(p_ccb)))
          else Local(LocalEvent.OpenChannelRsp(ConnectRspResult.Pending, l2c_csm_connection_mode(p_ccb)))
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG =>
        if (p_ccb.p_lcb_o != null && p_ccb.p_lcb_o.is_ble())
        then Local(OpenChannelRsp(ConnectRspResult.Refused, CreditBased))
        else Local(InternalFailure)
      case L2CEVT_L2CA_CONNECT_RSP_NEG =>
        Local(LocalEvent.OpenChannelRsp(
                ConnectRspResult.Refused,
                l2c_csm_connection_mode(p_ccb)
              ))
      case L2CEVT_TIMEOUT => Local(Timeout)
      case L2CEVT_L2CAP_DATA => Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE => Local(WriteData)
      case L2CEVT_L2CA_DISCONNECT_REQ => Local(LocalEvent.DisconnectReq)
      case L2CEVT_L2CAP_INFO_RSP => Packet(PeerInfoRsp(
                                             if (p_ccb.p_lcb_o != null && p_ccb.p_lcb_o.is_ble())
                                             then Ble
                                             else Classic
                                           ))
      case _ => Unmodeled
    }
  }
}
