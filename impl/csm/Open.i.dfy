module Impl.Csm.Open {
  import opened NativeTypes
  import opened AbsTypes
  import opened Constants
  import opened Types
  import opened ExternalTypes
  import opened External.Logging
  import opened CommonTypes

  import opened Utils
  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened Config
  import opened W4L2caDisconnectRsp
  import opened L2cCsmExtern.Helpers
  import opened CommonExtern

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_open(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT, p_data: DataPossibleView<ConfigAccessor>, p_le_data: DataPossibleView<ConfigAccessorLe>, p_buf: DataPossibleView<NativeHandle<BT_HDR>>, p_credit: DataPossibleView<uint16_t>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_OPEN)
             && p_ccb.p_lcb_o != null
    // functionality specifications
    requires (event in
                {
                  L2CEVT_L2CAP_CONFIG_REQ,
                  L2CEVT_L2CA_RECONFIG_REQ,
                  L2CEVT_L2CA_RECONFIG_RSP
                }
             ) ==> p_data.View?
    requires (event in
                {
                  L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ,
                  L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ
                }
             ) ==> p_le_data.View?
    requires (event in
                {
                  L2CEVT_L2CAP_DATA,
                  L2CEVT_L2CA_DATA_WRITE
                }
             ) ==> p_buf.View?
    requires (event in
                {
                  L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT,
                  L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT
                }
             ) ==> p_credit.View?
    requires event == L2CEVT_L2CAP_CONFIG_REQ || event == L2CEVT_L2CA_RECONFIG_REQ ==>
               && ((p_ccb.config_done & !IB_CFG_DONE) | IB_CFG_DONE) & OB_CFG_DONE == 0
    requires p_ccb.fcrb_num_tries() < UINT8_MAX
    modifies p_ccb`chnl_state,
             p_ccb`external_event, p_ccb`destroy_handle,
             p_ccb`p_lcb_o,
             p_ccb`config_done,
             //  p_ccb`peer_cfg,
             p_ccb`peer_conn_cfg,
             // Config related
             p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result,
             {}
    modifies p_ccb.p_lcb_o
    // state machine specifications
    requires !csm.IsDestroyedState()
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
    decreases RecursiveCount(event)
  {
    log_csm_execution_start("Open", CST_OPEN, event, p_ccb);

    csm.Execute(OpsEvent(event, p_ccb, p_credit));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        log_disconnect_ind("Open", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ =>
        /* For ecoc reconfig is handled below in l2c_ble. In case of success
         * let us notify upper layer about the reconfig
         */
        log("Open", Debug, "Calling LeReconfigCompleted_Cb(), " + fmt_cid(p_ccb));
        // (*p_ccb->p_rcb->api.pL2CA_CreditBasedReconfigCompleted_Cb)(
        //     p_ccb->p_lcb->remote_bd_addr(), p_ccb->local_cid, false, p_le_cfg);
        p_ccb.invoke_CreditBasedReconfigCompleted(true, p_le_data.view.GetExternalHandle());

      case L2CEVT_L2CAP_CONFIG_REQ /* Peer config request   */ =>

        // tempstate := p_ccb.chnl_state;
        // tempcfgdone := p_ccb.config_done;
        // p_ccb.chnl_state := CST_CONFIG;
        // // clear cached configuration in case reconfig takes place later
        // p_ccb.peer_cfg.mtu_present := false;
        // p_ccb.peer_cfg.flush_to_present := false;
        // p_ccb.peer_cfg.qos_present := false;
        // p_ccb.config_done := (p_ccb.config_done as bv8 | !(IB_CFG_DONE as bv8)) as uint8_t;

        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);

        var cfg_result := l2cu_process_peer_cfg_req(p_ccb.GetExternalHandle(), p_data.view.GetExternalHandle());
        if (cfg_result == L2CAP_PEER_CFG_OK) {
          // (*p_ccb->p_rcb->api.pL2CA_ConfigInd_Cb)(p_ccb->local_cid, p_cfg);
          // l2c_csm_send_config_rsp_ok(p_ccb);
          l2c_csm_open(csm, p_ccb, L2CEVT_L2CA_RECONFIG_REQ, p_data, p_le_data, p_buf, p_credit);
        }
        /* Error in config parameters: reset state and config flag */
        else if (cfg_result == L2CAP_PEER_CFG_UNACCEPTABLE) {
          alarm_cancel(p_ccb.GetExternalHandle());
          // p_ccb.chnl_state := tempstate;
          // p_ccb.config_done := tempcfgdone;
          l2c_csm_open(csm, p_ccb, L2CEVT_L2CA_RECONFIG_RSP, p_data, p_le_data, p_buf, p_credit); // l2cu_send_peer_config_rsp(csm, p_ccb, p_cfg);
        } else /* L2CAP_PEER_CFG_DISCONNECT */ {
          /* Disconnect if channels are incompatible
           * Note this should not occur if reconfigure
           * since this should have never passed original config.
           */
          l2c_csm_open(csm, p_ccb, L2CEVT_L2CA_CONFIG_RSP_NEG, p_data, p_le_data, p_buf, p_credit); // l2cu_disconnect_chnl(csm, p_ccb);
        }

      case L2CEVT_L2CAP_DISCONNECT_REQ /* Peer disconnected request */ =>
        if (!p_ccb.p_lcb_o.is_ble()) {
          var res := BTM_SetLinkPolicyActiveMode(p_ccb.p_lcb_o.remote_bd_addr());
          if (!res) {
            log("Open", Warn, "Unable to set link policy active");
          }
        }

        p_ccb.chnl_state := CST_W4_L2CA_DISCONNECT_RSP;
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);
        log_disconnect_ind("Open", true, p_ccb);
        p_ccb.invoke_DisconnectInd(true);
        if p_ccb.external_event.Some? {
          ExecuteAndAssumeSideEffects(
            csm,
            WaitLocalDisconnectResponse,
            W4L2caDisconnectRsp.OpsEvent(p_ccb.external_event.value, p_ccb),
            p_ccb
          );
          p_ccb.external_event := None;
        }
        if !p_ccb.IsDestroyed() {
          // Flattening of l2c_csm_send_disconnect_rsp
          l2c_csm_w4_l2ca_disconnect_rsp(csm, p_ccb, L2CEVT_L2CA_DISCONNECT_RSP, DataPossibleView.Unavailable);
        }

      case L2CEVT_L2CAP_DATA /* Peer data packet rcvd    */ =>
        p_ccb.invoke_DataIndWithMetrics(csm, p_buf.view);

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper layer disconnect request */ =>
        if (!p_ccb.p_lcb_o.is_ble()) {
          var res := BTM_SetLinkPolicyActiveMode(p_ccb.p_lcb_o.remote_bd_addr());
          if (!res) {
            log("Open", Warn, "Unable to set link policy active");
          }
        }

        if (p_ccb.p_lcb_o.is_ble()) {
          l2cble_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
        } else {
          l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
        }

        p_ccb.chnl_state := CST_W4_L2CAP_DISCONNECT_RSP;
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */ =>
        l2c_enqueue_peer_data(csm, p_ccb.GetExternalHandle(), p_buf.view);
        l2c_link_check_send_pkts_null(p_ccb.p_lcb_o.GetExternalHandle(), 0);

      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ =>
        p_ccb.chnl_state := CST_CONFIG;
        p_ccb.config_done := p_ccb.config_done & !OB_CFG_DONE;

        l2cu_send_credit_based_reconfig_req(csm, p_ccb.GetExternalHandle(), p_le_data.view.GetExternalHandle());

        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);

      case L2CEVT_L2CA_CONFIG_REQ /* Upper layer config req   */ =>
        log("Open", LogLevel.Error, "Dropping L2CAP re-config request because there is no usage and should not be invoked");

      case L2CEVT_TIMEOUT =>
        /* Process the monitor/retransmission time-outs in flow control/retrans
         * mode */
        if (p_ccb.peer_cfg_fcr_mode() != L2CAP_FCR_ERTM_MODE) {
          l2c_fcr_proc_tout(csm, p_ccb.GetExternalHandle());
        }
        // TODO: This is not necessarily true
        assume p_ccb.IsDestroyed();

      case L2CEVT_ACK_TIMEOUT =>
        l2c_fcr_proc_ack_tout(p_ccb.GetExternalHandle());

      case L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT =>
        log("Open", Debug, "Sending credit");
        l2cble_send_flow_control_credit(p_ccb.GetExternalHandle(), p_credit.view);

      case L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT =>
        var credit := p_credit.view;
        log("Open", Debug, "Credits received " + fmt_uint16("%d", credit));
        if (credit > L2CAP_LE_CREDIT_MAX - p_ccb.peer_conn_cfg.credits) {
          /* we have received credits more than max coc credits,
           * so disconnecting the Le Coc Channel
           */
          l2cble_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
          // FIXME: Model
          assume p_ccb.IsDestroyed();
        } else {
          p_ccb.peer_conn_cfg := p_ccb.peer_conn_cfg.(credits := p_ccb.peer_conn_cfg.credits + credit);
          l2c_link_check_send_pkts_null(p_ccb.p_lcb_o.GetExternalHandle(), 0);
        }

      /* Custom events to adjust state and perform actions */
      case L2CEVT_L2CA_RECONFIG_REQ =>
        p_ccb.chnl_state := CST_CONFIG;
        // clear cached configuration in case reconfig takes place later
        // p_ccb.peer_cfg := p_ccb.peer_cfg.(mtu_present := false, flush_to_present := false, qos_present := false);
        p_ccb.clear_cached_peer_cfg();
        p_ccb.config_done := p_ccb.config_done & !IB_CFG_DONE;
        p_ccb.invoke_ConfigInd(p_data.view); // (*p_ccb->p_rcb->api.pL2CA_ConfigInd_Cb)(p_ccb->local_cid, p_cfg);
        var p_cfg := l2c_csm_send_config_rsp_ok_get_cfg();
        l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_RSP, DataPossibleView.View(p_cfg), DataPossibleView.Unavailable, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2c_csm_send_config_rsp_ok(p_ccb);


      case L2CEVT_L2CA_CONFIG_RSP_NEG =>
        l2cu_disconnect_chnl(csm, p_ccb.GetExternalHandle());

      case L2CEVT_L2CA_RECONFIG_RSP =>
        alarm_cancel(p_ccb.GetExternalHandle());
        l2cu_send_peer_config_rsp(csm, p_ccb.GetExternalHandle(), p_data.view.GetExternalHandle());

      case _ =>
        log("Open", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("Open", p_ccb.chnl_state, event);
  }

  ghost function RecursiveCount(event: tL2CEVT): int {
    if event == L2CEVT_L2CAP_CONFIG_REQ then
      1
    else 0
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB, p_credit: DataPossibleView<uint16_t>): OsmEvent
    reads p_ccb,
          p_ccb`peer_conn_cfg, p_ccb`peer_conn_cfg
    requires p_ccb.fcrb_num_tries() < UINT8_MAX
    requires event == L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT ==> p_credit.View?
  {
    match (event) {
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP =>
        Packet(PacketEvent.ConfigRsp(ConfigResult.Success))
      case L2CEVT_L2CAP_CONFIG_REQ =>
        Packet(PacketEvent.ConfigReq(false))
      case L2CEVT_L2CA_RECONFIG_REQ =>
        Local(LocalEvent.ConfigReq(ConfigResult.Success))
      case L2CEVT_L2CA_CONFIG_RSP_NEG =>
        if (p_ccb.local_cid() >= L2CAP_BASE_APPL_CID)
        then Local(LocalEvent.ConfigRsp(ConfigResult.Failure(true)))
        else Local(LocalEvent.ConfigRsp(ConfigResult.Failure(false)))
      case L2CEVT_L2CA_RECONFIG_RSP =>
        Local(LocalEvent.ConfigRsp(Reconfig))
      case L2CEVT_L2CAP_DISCONNECT_REQ =>
        Packet(PacketEvent.DisconnectReq)
      case L2CEVT_L2CAP_DATA =>
        Packet(PacketEvent.Data)
      case L2CEVT_L2CA_DISCONNECT_REQ =>
        Local(LocalEvent.DisconnectReq)
      case L2CEVT_L2CA_DATA_WRITE =>
        Local(WriteData)
      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ =>
        Local(LocalEvent.ConfigReq(Reconfig))
      case L2CEVT_TIMEOUT =>
        if p_ccb.peer_cfg_fcr_mode() != L2CAP_FCR_ERTM_MODE
           && p_ccb.peer_cfg_fcr_max_transmit() != 0
           && p_ccb.fcrb_num_tries() + 1 > p_ccb.peer_cfg_fcr_max_transmit()
           && p_ccb.local_cid() >= L2CAP_BASE_APPL_CID
        then Local(Timeout)
        else Local(InternalFailure)
      case L2CEVT_L2CA_CONFIG_REQ
        | L2CEVT_ACK_TIMEOUT
        => Unmodeled
      case L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT =>
        Local(SendCredit)
      case L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT =>
        if ((p_ccb.peer_conn_cfg.credits as int + p_credit.view as int) > L2CAP_LE_CREDIT_MAX as int)
        then Packet(Credit(true))
        else Packet(Credit(false))
      case _ => Unmodeled
    }
  }
}
