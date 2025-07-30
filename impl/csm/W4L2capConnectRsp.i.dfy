module Impl.Csm.W4L2capConnectRsp {
  import opened Constants
  import opened Types
  import opened External.Logging
  import opened Utils

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened L2cCsmExtern.Helpers
  import opened Config

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_w4_l2cap_connect_rsp(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT, p_ci: DataPossibleView<tL2C_CONN_INFO>, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_W4_L2CAP_CONNECT_RSP)
    // functionality specifications
    requires match event {
               case
                 | L2CEVT_L2CAP_CONNECT_RSP
                 | L2CEVT_L2CAP_CONNECT_RSP_PND
                 | L2CEVT_L2CAP_CONNECT_RSP_NEG
                 | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP
                 | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG
                 | L2CEVT_L2CAP_INFO_RSP
                 | L2CEVT_TIMEOUT =>
                 true
               case L2CEVT_L2CA_DISCONNECT_REQ => p_ccb.remote_cid != 0
               case _ => false
             }
             ==> p_ccb.p_lcb_o != null
    requires (event in
                {
                  L2CEVT_L2CAP_CONNECT_RSP,
                  L2CEVT_L2CAP_CONNECT_RSP_PND,
                  L2CEVT_L2CAP_CONNECT_RSP_NEG,
                  L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP,
                  L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG
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
               case
                 |  L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP
                 | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG => true
               case _ => false
             }
             ==> p_ccb.p_lcb_o.is_ble()
    requires p_ccb.flags & CCB_FLAG_NO_RETRY == 0 ==> !csm.no_retry
    modifies p_ccb`chnl_state,
             p_ccb`external_event, p_ccb`destroy_handle,
             p_ccb`p_lcb_o,
             p_ccb`flags,
             p_ccb`remote_cid,
             p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result
    modifies p_ccb.p_lcb_o
    // state machine specifications
    requires !csm.IsDestroyedState()
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
  {
    log_csm_execution_start("W4L2capConnectRsp", CST_W4_L2CAP_CONNECT_RSP, event, p_ccb);

    csm.Execute(OpsEvent(event, p_ccb));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        /* Send disc indication unless peer to peer race condition AND normal
         * disconnect */
        /* *((uint8_t *)p_data) != HCI_ERR_PEER_USER happens when peer device try
         * to disconnect for normal reason */
        p_ccb.chnl_state := CST_CLOSED;
        if (p_ccb.flags & CCB_FLAG_NO_RETRY != 0 || (p_ci.View? ==> p_ci.view.status() != HCI_ERR_PEER_USER)) {
          log_disconnect_ind("W4L2capConnectRsp", false, p_ccb);
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
          p_ccb.invoke_DisconnectInd(false);
        } else {
          csm.Retry();
        }
        p_ccb.flags := p_ccb.flags | CCB_FLAG_NO_RETRY;


      case L2CEVT_L2CAP_CONNECT_RSP /* Got peer connect confirm */ =>
        p_ccb.remote_cid := p_ci.view.remote_cid();
        if (p_ccb.p_lcb_o.is_ble()) {
          /* Connection is completed */
          alarm_cancel(p_ccb.GetExternalHandle());
          p_ccb.chnl_state := CST_OPEN;
          l2c_csm_indicate_connection_open(p_ccb.GetExternalHandle());
          p_ccb.init_le_coc_configs();
          return; // l2c_csm_execute(p_ccb.GetExternalHandle(), L2CEVT_L2CA_CONNECT_RSP, NULL);
        } else {
          p_ccb.chnl_state := CST_CONFIG;
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);
        }
        log("W4L2capConnectRsp", Debug, "Calling Connect_Cfm_Cb(), " + fmt_cid(p_ccb) + ", Success");

        var cfg := l2c_csm_send_config_req_set_and_get_our_cfg(p_ccb.GetExternalHandle());
        l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_REQ, DataPossibleView.View(cfg), DataPossibleView.Unavailable, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2c_csm_send_config_req(p_ccb);

      case L2CEVT_L2CAP_CONNECT_RSP_PND /* Got peer connect pending */ =>
        p_ccb.remote_cid := p_ci.view.remote_cid();
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_EXT_TIMEOUT_MS);

      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP =>
        alarm_cancel(p_ccb.GetExternalHandle());
        p_ccb.chnl_state := CST_OPEN;
        log("W4L2capConnectRsp", Debug, "Calling credit_based_connect_cfm()," +
            fmt_uint16("cid %d", p_ccb.local_cid()) + ", " +
            fmt_uint16("result 0x%04x", L2CAP_CONN_OK));

        p_ccb.invoke_CreditBasedConnectCfm(p_ci.view.peer_mtu(), L2CAP_CONN_OK);

      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG =>
        log("W4L2capConnectRsp", Debug, "Calling pL2CA_Error_Cb()," +
            fmt_uint16("cid %d", p_ccb.local_cid()) + ", " +
            fmt_uint16("result 0x%04x", L2CAP_CONN_OK));
        p_ccb.invoke_Error(p_ci.view.l2cap_result());

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_L2CAP_CONNECT_RSP_NEG /* Peer rejected connection */ =>
        log("W4L2capConnectRsp", Warn, "l2c_csm_w4_l2cap_connect_rsp: L2CAP connection rejected, " + fmt_uint16("lcid=%x",p_ccb.local_cid()) + fmt_uint16(", reason=%d",        p_ci.view.l2cap_result()));

        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);

      case L2CEVT_TIMEOUT =>
        log("W4L2capConnectRsp", Warn, "l2c_csm_w4_l2cap_connect_rsp: L2CAP connection timeout");

        if (p_ccb.ecoc()) {
          // for (int i = 0; i < p_lcb->pending_ecoc_conn_cnt; i++) {
          //   uint16_t cid = p_lcb->pending_ecoc_connection_cids[i];
          //   tL2C_CCB* temp_p_ccb = l2cu_find_ccb_by_cid(p_lcb, cid);
          //   LOG(WARNING) << __func__ << ": lcid= " << loghex(cid);
          //   (*p_ccb->p_rcb->api.pL2CA_Error_Cb)(p_ccb->local_cid,
          //                                       L2CAP_CONN_TIMEOUT);
          //   l2cu_release_ccb(temp_p_ccb);
          // }
          // p_lcb->pending_ecoc_conn_cnt = 0;
          // memset(p_lcb->pending_ecoc_connection_cids, 0,
          //       L2CAP_CREDIT_BASED_MAX_CIDS);

          // NOTE: the above logic will be modeled as a separate function.
          l2c_csm_close_credit_based_conn(csm, p_ccb.GetExternalHandle(), false);
        } else {
          log("W4L2capConnectRsp", Warn, "l2c_csm_w4_l2cap_connect_rsp: " + fmt_uint16("lcid=%d", p_ccb.local_cid()));
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
          p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);
        }

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper wants to disconnect */ =>
        /* If we know peer CID from connect pending, we can send disconnect */
        if (p_ccb.remote_cid != 0) {
          l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
          p_ccb.chnl_state := CST_W4_L2CAP_DISCONNECT_RSP;
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);
        } else {
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        }

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */
        | L2CEVT_L2CAP_DATA      /* Peer data packet rcvd */ =>
        l2c_csm_osi_free(p_data.view);

      case L2CEVT_L2CAP_INFO_RSP =>
        /* Need to have at least one compatible channel to continue */
        var res := l2c_fcr_chk_chan_modes(p_ccb.GetExternalHandle());
        if (!res) {
          l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
          p_ccb.invoke_Error(L2CAP_CONN_OTHER_ERROR);
        } else {
          /* We have feature info, so now send peer connect request */
          alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CONNECT_TIMEOUT_MS);
          l2cu_send_peer_connect_req(csm, p_ccb.GetExternalHandle()); /* Start Connection */
        }

      case _ =>
        log("W4L2capConnectRsp", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("W4L2capConnectRsp", p_ccb.chnl_state, event);
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB) : OsmEvent
    reads p_ccb,
          p_ccb.p_lcb_o
    requires match event {
               case L2CEVT_L2CAP_CONNECT_RSP
                 | L2CEVT_L2CAP_CONNECT_RSP_PND
                 | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP
                 | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG
                 | L2CEVT_L2CAP_CONNECT_RSP_NEG
                 | L2CEVT_L2CAP_INFO_RSP
                 => p_ccb.p_lcb_o != null
               case _ => true
             }
  {
    match (event) {
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_L2CAP_CONNECT_RSP =>
        Packet(ConnectRsp(ConnectRspResult.Success, l2c_csm_connection_mode(p_ccb)))
      case L2CEVT_L2CAP_CONNECT_RSP_PND =>
        Packet(ConnectRsp(ConnectRspResult.Pending, l2c_csm_connection_mode(p_ccb)))
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP =>
        Packet(ConnectRsp(ConnectRspResult.Success, CreditBased))
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG =>
        Packet(ConnectRsp(ConnectRspResult.Refused, CreditBased))
      case L2CEVT_L2CAP_CONNECT_RSP_NEG =>
        Packet(ConnectRsp(ConnectRspResult.Refused, l2c_csm_connection_mode(p_ccb)))
      case L2CEVT_TIMEOUT => Local(Timeout)
      case L2CEVT_L2CA_DISCONNECT_REQ =>
        if p_ccb.remote_cid != 0
        then Local(LocalEvent.DisconnectReq)
        else Local(InternalFailure)
      case L2CEVT_L2CAP_DATA => Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE => Local(WriteData)
      case L2CEVT_L2CAP_INFO_RSP =>
        if l2c_csm_incompatible_channels(p_ccb)
        then Local(InternalFailure)
        else Packet(PeerInfoRsp(
                      if (p_ccb.p_lcb_o != null && p_ccb.p_lcb_o.is_ble())
                      then Ble
                      else Classic
                    ))
      case _ => Unmodeled
    }
  }
}
