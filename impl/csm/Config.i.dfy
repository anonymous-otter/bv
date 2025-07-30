module Impl.Csm.Config {
  import opened ExternalTypes
  import opened Constants
  import opened Types
  import opened External.Logging
  import opened Utils
  import opened CommonTypes

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern
  import opened W4L2caDisconnectRsp
  import opened L2cCsmExtern.Helpers

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_config(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT , p_cfg_data: DataPossibleView<ConfigAccessor>, p_le_data: DataPossibleView<ConfigAccessorLe>, p_buf: DataPossibleView<NativeHandle<BT_HDR>>, p_data: DataPossibleView<IgnorableData>)
    // functionality specifications
    requires && p_ccb.chnl_state == CST_CONFIG
             && !p_ccb.IsDestroyed()
             && p_ccb.p_lcb_o != null
    requires (event in
                {
                  L2CEVT_L2CAP_CONFIG_REQ,
                  L2CEVT_L2CAP_CONFIG_RSP,
                  L2CEVT_L2CAP_CONFIG_RSP_NEG,
                  L2CEVT_L2CA_CONFIG_REQ,
                  L2CEVT_L2CA_CONFIG_RSP,
                  L2CEVT_L2CA_RECONFIG_RSP
                }
             ) ==> p_cfg_data.View?
    requires (event in
                {
                  L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ,
                  L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP,
                  L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ
                }
             ) ==> p_le_data.View?
    requires ((event in
                 {
                   L2CEVT_L2CAP_DATA,
                   L2CEVT_L2CA_DATA_WRITE
                 }
              ) && p_ccb.config_done & 0x02 != 0) ==> p_buf.View?
    requires event == L2CEVT_L2CAP_DATA ==> p_buf.View?
    requires ((event in
                 {
                   L2CEVT_L2CA_DATA_WRITE
                 }
              ) && p_ccb.config_done & 0x02 == 0) ==> p_data.View?
    requires event == L2CEVT_L2CAP_CONFIG_RSP_NEG ==> p_ccb.fcr_cfg_tries > 0

    // ensures p_ccb.copy_our_cfg() != old(p_ccb.copy_our_cfg())
    // state machine specifications
    requires !csm.IsDestroyedState()
    // requires IsValidStateMachine(csm, p_ccb)
    requires IsValidStateMachine(csm, p_ccb)
    modifies p_ccb.p_lcb_o
    modifies p_ccb`chnl_state,
             p_ccb`external_event, p_ccb`destroy_handle,
             p_ccb`p_lcb_o,
             // Config related
             p_ccb`fcr_cfg_tries,
             p_ccb`config_done,
             p_ccb`remote_config_rsp_result,
             {}

    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
    decreases RecursiveCount(event)
  {
    log_csm_execution_start("Config", CST_CONFIG, event, p_ccb);

    var p_cfg := p_cfg_data;
    var p_le_cfg := p_le_data;

    csm.Execute(OpsEvent(event, p_ccb));

    match (event) {
      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */ =>
        log_disconnect_ind("Config", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ =>
        /* For ecoc reconfig is handled below in l2c_ble. In case of success
         * let us notify upper layer about the reconfig
         */
        log("Config", Debug, "Calling LeReconfigCompleted_Cb(), " + fmt_cid(p_ccb));
        p_ccb.invoke_CreditBasedReconfigCompleted(false, p_le_cfg.view.GetExternalHandle());

      case L2CEVT_L2CAP_CONFIG_REQ /* Peer config request   */ =>
        var cfg_result := l2cu_process_peer_cfg_req(p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());
        if (cfg_result == L2CAP_PEER_CFG_OK) {
          log("Config", Debug, "Calling Config_Req_Cb(), " + fmt_cid(p_ccb) + ", " + fmt_uint16("C-bit %d", (p_cfg.view.flags() as bv16 & L2CAP_CFG_FLAGS_MASK_CONT) as uint16_t));

          // Flattening of l2c_csm_send_config_rsp_ok(p_ccb);
          var cfg := l2c_csm_send_config_rsp_ok_get_cfg();
          l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_RSP, DataPossibleView.View(cfg), DataPossibleView.Unavailable, DataPossibleView.Unavailable, DataPossibleView.Unavailable);
          if (p_ccb.config_done & OB_CFG_DONE != 0) {
            if (p_ccb.remote_config_rsp_result == L2CAP_CFG_OK) {
              l2c_csm_indicate_connection_open(p_ccb.GetExternalHandle());
            } else {
              var connection_initiator := if (p_ccb.connection_initiator()) then 1 else 0;
              if (connection_initiator == L2CAP_INITIATOR_LOCAL) {
                p_ccb.invoke_Error(L2CAP_CFG_FAILED_NO_REASON);
              }
            }
          }
        } else if (cfg_result == L2CAP_PEER_CFG_DISCONNECT) {
          /* Disconnect if channels are incompatible */
          l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_RSP_NEG, p_cfg, p_le_cfg, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2cu_disconnect_chnl(csm, p_ccb);
        } else /* Return error to peer so it can renegotiate if possible */ {
          l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_RECONFIG_RSP, p_cfg, p_le_cfg, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2cu_send_peer_config_rsp(csm, p_ccb, p_cfg);
        }

      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP =>
        p_ccb.config_done := p_ccb.config_done | OB_CFG_DONE;
        p_ccb.config_done := p_ccb.config_done | RECONFIG_FLAG;
        p_ccb.chnl_state := CST_OPEN;
        alarm_cancel(p_ccb.GetExternalHandle());

        log("Config", Debug, "Calling Config_Rsp_Cb(), " + fmt_cid(p_ccb));
        p_ccb.invoke_CreditBasedReconfigCompleted(true, p_le_cfg.view.GetExternalHandle());

      case L2CEVT_L2CAP_CONFIG_RSP /* Peer config response  */ =>
        l2cu_process_peer_cfg_rsp(p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());

        /* TBD: When config options grow beyong minimum MTU (48 bytes)
         *      logic needs to be added to handle responses with
         *      continuation bit set in flags field.
         *       1. Send additional config request out until C-bit is cleared in
         * response
         */
        p_ccb.config_done := p_ccb.config_done | OB_CFG_DONE;

        if (p_ccb.config_done & IB_CFG_DONE != 0) {
          /* Verify two sides are in compatible modes before continuing */
          if (p_ccb.our_cfg_fcr_mode() != p_ccb.peer_cfg_fcr_mode()) {
            l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
            log_disconnect_ind_incompatible("Config", p_ccb);
            l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
            p_ccb.invoke_DisconnectInd(false);
            return;
          }

          p_ccb.config_done := p_ccb.config_done | RECONFIG_FLAG;
          p_ccb.chnl_state := CST_OPEN;
          l2c_link_adjust_allocation();
          alarm_cancel(p_ccb.GetExternalHandle());

          /* If using eRTM and waiting for an ACK, restart the ACK timer */
          if (p_ccb.fcrb_wait_ack()) {
            l2c_fcr_start_timer(p_ccb.GetExternalHandle());
          }

          /*
           ** check p_ccb->our_cfg.fcr.mon_tout and
           *p_ccb->our_cfg.fcr.rtrans_tout
           ** we may set them to zero when sending config request during
           *renegotiation
           */
          var our_cfg := p_ccb.copy_our_cfg();
          if ((our_cfg.fcr.mode == L2CAP_FCR_ERTM_MODE) &&
              ((our_cfg.fcr.mon_tout == 0) ||
               (our_cfg.fcr.rtrans_tout != 0))) {
            l2c_fcr_adj_monitor_retran_timeout(p_ccb.GetExternalHandle());
          }

          /* See if we can forward anything on the hold queue */
          var res := xmit_hold_queue_is_empty(p_ccb.GetExternalHandle());
          if (!res) {
            l2c_link_check_send_pkts_null(p_ccb.p_lcb_o.GetExternalHandle(), 0);
          }
        }

        log("Config", Debug, "Calling Config_Rsp_Cb(), " + fmt_cid(p_ccb));
        p_ccb.remote_config_rsp_result := p_cfg.view.copy().result;
        if (p_ccb.config_done & IB_CFG_DONE != 0) {
          l2c_csm_indicate_connection_open(p_ccb.GetExternalHandle());
        }

      case L2CEVT_L2CAP_CONFIG_RSP_NEG /* Peer config error rsp */ =>
        /* Disable the Timer */
        alarm_cancel(p_ccb.GetExternalHandle());

        // ------ Start of l2c_fcr_renegotiate_chan(p_ccb, p_cfg) ------

        /* If failure was channel mode try to renegotiate */
        var peer_mode: uint8_t := p_ccb.peer_cfg_fcr_mode();
        var can_renegotiate: bool := false;

        /* Skip if this is a reconfiguration from OPEN STATE or if FCR is not returned
         */
        var cfg := p_cfg.view.copy();
        var our_cfg := p_ccb.copy_our_cfg();

        if (!cfg.fcr_present || p_ccb.config_done & RECONFIG_FLAG != 0) {
          can_renegotiate := false;
        } else {
          /* Only retry if there are more channel options to try */
          if (cfg.result == L2CAP_CFG_UNACCEPTABLE_PARAMS as uint16_t) {
            peer_mode := if (cfg.fcr_present) then cfg.fcr.mode else L2CAP_FCR_BASIC_MODE;

            if (our_cfg.fcr.mode != peer_mode) {
              p_ccb.fcr_cfg_tries := p_ccb.fcr_cfg_tries - 1;
              if (p_ccb.fcr_cfg_tries == 0) {
                cfg := cfg.(result := L2CAP_CFG_FAILED_NO_REASON as uint16_t);
                log("Config", Warn, "l2c_fcr_renegotiate_chan (Max retries exceeded)");
              }

              can_renegotiate := false;

              /* Try another supported mode if available based on our last attempted
               * channel */
              if (our_cfg.fcr.mode == L2CAP_FCR_ERTM_MODE) {
                /* We can try basic for any other peer mode if we support it */
                if ((p_ccb.rcb_ertm_info_preferred_mode() as bv8 & L2CAP_FCR_BASIC_MODE as bv8) as uint8_t != 0) {
                  log("Config", Debug, "l2c_fcr_renegotiate_chan(Trying Basic)");
                  can_renegotiate := true;
                  our_cfg := our_cfg.(fcr := our_cfg.fcr.(mode := L2CAP_FCR_BASIC_MODE));
                }
              }

              if (can_renegotiate) {
                our_cfg := our_cfg.(fcr_present := true);

                if (our_cfg.fcr.mode == L2CAP_FCR_BASIC_MODE) {
                  our_cfg := our_cfg.(fcr_present := false);
                  our_cfg := our_cfg.(ext_flow_spec_present := false);

                  /* Basic Mode uses ACL Data Pool, make sure the MTU fits */
                  if (cfg.mtu_present && cfg.mtu > L2CAP_MTU_SIZE) {
                    log("Config", Warn, fmt_uint16("L2CAP - adjust MTU: %u too large", cfg.mtu));
                    our_cfg := our_cfg.(mtu := L2CAP_MTU_SIZE);
                  }
                }


                // l2cu_process_our_cfg_req(p_ccb, &p_ccb->our_cfg);
                // l2cu_send_peer_config_req(p_ccb, &p_ccb->our_cfg);
                // alarm_set_on_mloop(p_ccb->l2c_ccb_timer, L2CAP_CHNL_CFG_TIMEOUT_MS,
                //                   l2c_ccb_timer_timeout, p_ccb);
                l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_RECONFIG_REQ, p_cfg, p_le_cfg, DataPossibleView.Unavailable, DataPossibleView.Unavailable);
              }
            }
          }

          /* Disconnect if the channels do not match */
          if (our_cfg.fcr.mode != peer_mode) {
            log("Config", Warn, "L2C CFG:  Channels incompatible (" + fmt_uint8("local %d", our_cfg.fcr.mode) + fmt_uint8(", peer %d", peer_mode) + ")");
            l2c_csm_config(csm, p_ccb, L2CEVT_L2CA_CONFIG_RSP_NEG, p_cfg, p_le_cfg, DataPossibleView.Unavailable, DataPossibleView.Unavailable); // l2cu_disconnect_chnl(csm, p_ccb);
          }
        }
        p_ccb.update_our_cfg(our_cfg);
        p_cfg.view.update(cfg);

        // ------ End of l2c_fcr_renegotiate_chan(p_ccb, p_cfg) ------


        if (!can_renegotiate) {
          log("Config", Debug, "Calling Config_Rsp_Cb(), " + fmt_cid(p_ccb) + ", " + fmt_uint16("Failure: %d", cfg.result));
          var connection_initiator := if (p_ccb.connection_initiator()) then 1 else 0;
          if (connection_initiator == L2CAP_INITIATOR_LOCAL) {
            p_ccb.invoke_Error(L2CAP_CFG_FAILED_NO_REASON as uint16_t);
          }
        }

      case L2CEVT_L2CAP_DISCONNECT_REQ /* Peer disconnected request */ =>
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);
        p_ccb.chnl_state := CST_W4_L2CA_DISCONNECT_RSP;
        log_disconnect_ind("Config", true, p_ccb);
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
          l2c_csm_w4_l2ca_disconnect_rsp(csm, p_ccb, L2CEVT_L2CA_DISCONNECT_RSP, DataPossibleView.Unavailable);
        }

      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ =>
        l2cu_send_credit_based_reconfig_req(csm, p_ccb.GetExternalHandle(), p_le_cfg.view.GetExternalHandle());
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);

      case L2CEVT_L2CA_CONFIG_REQ /* Upper layer config req   */ =>
        l2cu_process_our_cfg_req_and_send_peer(csm, p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);

      case L2CEVT_L2CA_CONFIG_RSP /* Upper layer config rsp   */ =>
        l2cu_process_our_cfg_rsp(p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());

        p_ccb.config_done := p_ccb.config_done | IB_CFG_DONE;

        if ((p_ccb.config_done & OB_CFG_DONE) != 0) {
          /* Verify two sides are in compatible modes before continuing */
          if (p_ccb.our_cfg_fcr_mode() != p_ccb.peer_cfg_fcr_mode()) {
            l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
            log_disconnect_ind_incompatible("Config", p_ccb);
            l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
            p_ccb.invoke_DisconnectInd(false);
            return;
          }

          p_ccb.config_done := p_ccb.config_done | RECONFIG_FLAG;
          p_ccb.chnl_state := CST_OPEN;
          l2c_link_adjust_allocation();
          alarm_cancel(p_ccb.GetExternalHandle());
        }

        l2cu_send_peer_config_rsp(csm, p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());

        /* If using eRTM and waiting for an ACK, restart the ACK timer */
        if (p_ccb.fcrb_wait_ack()) {
          l2c_fcr_start_timer(p_ccb.GetExternalHandle());
        }

        /* See if we can forward anything on the hold queue */
        var res := xmit_hold_queue_is_empty(p_ccb.GetExternalHandle());
        if ((p_ccb.chnl_state == CST_OPEN) && (!res)) {
          l2c_link_check_send_pkts_null(p_ccb.p_lcb_o.GetExternalHandle(), 0);
        }

      case L2CEVT_L2CA_DISCONNECT_REQ /* Upper wants to disconnect */ =>
        l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
        p_ccb.chnl_state := CST_W4_L2CAP_DISCONNECT_RSP;
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_DISCONNECT_TIMEOUT_MS);

      case L2CEVT_L2CAP_DATA /* Peer data packet rcvd    */ =>
        log("Config", Debug, "Calling DataInd_Cb(), " + fmt_cid(p_ccb));
        if (p_ccb.local_cid() >= L2CAP_FIRST_FIXED_CHNL &&
            p_ccb.local_cid() <= L2CAP_LAST_FIXED_CHNL) {
          if (p_ccb.local_cid() < L2CAP_BASE_APPL_CID) {
            // if (l2cb.fixed_reg[p_ccb->local_cid - L2CAP_FIRST_FIXED_CHNL]
            //         .pL2CA_FixedData_Cb != nullptr) {
            //   p_ccb->metrics.rx(static_cast<BT_HDR*>(p_data)->len);
            //   (*l2cb.fixed_reg[p_ccb->local_cid - L2CAP_FIRST_FIXED_CHNL]
            //         .pL2CA_FixedData_Cb)(p_ccb->local_cid,
            //                             p_ccb->p_lcb->remote_bd_addr,
            //                             (BT_HDR*)p_data);
            // } else {
            //   if (p_data != nullptr) osi_free_and_reset(&p_data);
            // }
            l2c_csm_config_fixed_data_ind(csm, p_ccb.GetExternalHandle(), p_buf.view);
            return;
          }
        }
        p_ccb.invoke_DataIndWithMetrics(csm, p_buf.view);

      case L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */ =>
        if (p_ccb.config_done & 0x02 != 0) { // OB_CFG_DONE = 0x02
          l2c_enqueue_peer_data(csm, p_ccb.GetExternalHandle(), p_buf.view);
        } else {
          l2c_csm_osi_free(p_data.view);
        }

      case L2CEVT_TIMEOUT =>
        if (p_ccb.ecoc()) {
          l2c_csm_close_config_conn(csm, p_ccb.GetExternalHandle());
          acl_disconnect_from_handle(p_ccb.GetExternalHandle(), HCI_ERR_CONN_CAUSE_LOCAL_HOST);
          return;
        }

        l2cu_send_peer_disc_req(csm, p_ccb.GetExternalHandle());
        log_disconnect_ind("Config", false, p_ccb);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());
        p_ccb.invoke_DisconnectInd(false);

      /* Custom events to perform actions */

      case L2CEVT_L2CA_CONFIG_RSP_NEG =>
        log("Config", Debug, "incompatible configurations disconnect");
        l2cu_disconnect_chnl(csm, p_ccb.GetExternalHandle());

      case L2CEVT_L2CA_RECONFIG_RSP =>
        log("Config", Debug, "incompatible configurations trying reconfig");
        l2cu_send_peer_config_rsp(csm, p_ccb.GetExternalHandle(), p_cfg.view.GetExternalHandle());

      case L2CEVT_L2CA_RECONFIG_REQ =>
        l2cu_process_our_cfg_req_and_send_peer_from_our_cfg(csm, p_ccb.GetExternalHandle());
        alarm_set_on_mloop(p_ccb.GetExternalHandle(), L2CAP_CHNL_CFG_TIMEOUT_MS);

      case _ =>
        log("Config", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }
    log_csm_execution_exit("Config", p_ccb.chnl_state, event);
  }

  ghost function RecursiveCount(event: tL2CEVT): int {
    if event == L2CEVT_L2CAP_CONFIG_REQ || event == L2CEVT_L2CAP_CONFIG_RSP_NEG then
      1
    else 0
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB): OsmEvent
    // requires p_ccb.p_rcb_o != null
    reads p_ccb,
          // p_ccb`our_cfg, p_ccb`our_cfg
          {}
  {
    match event {
      case L2CEVT_LP_DISCONNECT_IND => Local(LinkDisconnectInd)
      case L2CEVT_L2CAP_CONFIG_REQ => Unmodeled
      // Packet(PacketEvent.ConfigReq(false))
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP =>
        Packet(PacketEvent.ConfigRsp(ConfigResult.Success))
      case L2CEVT_L2CAP_CONFIG_RSP =>
        if (p_ccb.config_done & IB_CFG_DONE != 0) then
          if (p_ccb.our_cfg_fcr_mode() != p_ccb.peer_cfg_fcr_mode())
          then Packet(PacketEvent.ConfigRsp(ConfigResult.Failure(true)))
          else Packet(PacketEvent.ConfigRsp(ConfigResult.Success))
        else Packet(PacketEvent.ConfigRsp(ConfigResult.Pending))
      case L2CEVT_L2CA_CONFIG_RSP_NEG =>
        if (p_ccb.local_cid() >= L2CAP_BASE_APPL_CID)
        then Local(LocalEvent.ConfigRsp(ConfigResult.Failure(true)))
        else Local(LocalEvent.ConfigRsp(ConfigResult.Failure(false)))
      case L2CEVT_L2CA_RECONFIG_RSP =>
        Local(LocalEvent.ConfigRsp(Reconfig))
      case L2CEVT_L2CA_RECONFIG_REQ =>
        Local(LocalEvent.ConfigReq(Reconfig))
      case L2CEVT_L2CAP_DISCONNECT_REQ =>
        Packet(PacketEvent.DisconnectReq)
      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ =>
        Local(LocalEvent.ConfigReq(Reconfig))
      case L2CEVT_L2CA_CONFIG_REQ =>
        Local(LocalEvent.ConfigReq(ConfigResult.Success))
      case L2CEVT_L2CA_CONFIG_RSP =>
        if ((p_ccb.config_done | IB_CFG_DONE) & OB_CFG_DONE != 0) then
          if (p_ccb.our_cfg_fcr_mode() != p_ccb.peer_cfg_fcr_mode())
          then Local(LocalEvent.ConfigRsp(ConfigResult.Failure(true)))
          else Packet(PacketEvent.ConfigReq(true)) // Local(LocalEvent.ConfigRsp(ConfigResult.Success))
        else Packet(PacketEvent.ConfigReq(false)) // Local(LocalEvent.ConfigRsp(Reconfig))
      case L2CEVT_L2CA_DISCONNECT_REQ =>
        Local(LocalEvent.DisconnectReq)
      case L2CEVT_L2CAP_DATA =>
        Packet(Data)
      case L2CEVT_L2CA_DATA_WRITE =>
        if ((p_ccb.config_done & OB_CFG_DONE) != 0) then Local(WriteData)
        else Unmodeled
      case L2CEVT_TIMEOUT =>
        if p_ccb.ecoc() then Local(InternalFailure)
        else Local(Timeout)
      // by default ignore other events
      case _ => Unmodeled
    }
  }
}
