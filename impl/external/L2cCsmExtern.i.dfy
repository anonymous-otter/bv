module Impl.L2cCsmExtern {
  import opened NativeTypes
  import opened ExternalTypes
  import opened AbsTypes
  import opened Types
  import opened OpaqueTypes

  import opened Constants

  import opened OpsStateMachine
  import opened Utils
  import opened L2cCsmOsm

  // Utils

  method {:extern "stack_extern", "se_l2cu_release_ccb"} {:axiom} l2cu_release_ccb(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    modifies h_ccb.obj`p_lcb_o
    ensures h_ccb.obj.IsDestroyed()

  method {:extern "stack_extern", "se_l2cu_send_peer_connect_req"} {:axiom} l2cu_send_peer_connect_req(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConnectReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectReq]

  method {:extern "stack_extern", "se_l2cu_reject_ble_connection"} {:axiom} l2cu_reject_ble_connection(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, remote_id: uint8_t, result: tL2CAP_LE_RESULT_CODE)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConnectRspSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(Refused)]

  method {:extern "stack_extern", "se_l2cu_send_peer_connect_rsp"} {:axiom} l2cu_send_peer_connect_rsp(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, result: uint16_t, status: uint16_t)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies h_ccb.obj`flags
    modifies csm`footprint
    ensures IsPeerConnectRspSent()
    ensures match result {
              case L2CAP_CONN_OK => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(ConnectRspResult.Success)]
              case L2CAP_CONN_PENDING => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(ConnectRspResult.Pending)]
              case _ => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(Refused)]
            }

  method {:extern "stack_extern", "se_l2cu_send_peer_disc_req"} {:axiom} l2cu_send_peer_disc_req(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerDisconnectReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendDisconnectReq]

  method {:extern "stack_extern", "se_l2cu_send_peer_disc_rsp"} {:axiom} l2cu_send_peer_disc_rsp(ghost csm: L2cCsm, h_lcb: ExternalHandle<tL2C_LCB>, remote_id: uint8_t, local_cid: uint16_t, remote_cid: uint16_t)
    modifies h_lcb.obj
    modifies csm`footprint
    ensures IsPeerDisconnectRspSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendDisconnectRsp]

  method {:extern "stack_extern", "se_l2cu_send_peer_credit_based_conn_res"} {:axiom} l2cu_send_peer_credit_based_conn_res(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, h_ci: ExternalHandle<tL2C_CONN_INFO>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConnectRspSent()
    ensures match h_ci.obj.l2cap_result() {
              case L2CAP_CONN_OK => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(ConnectRspResult.Success)]
              case _ => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(Refused)]
            }

  // NOTE: It calls release internally
  method {:extern "stack_extern", "se_l2cu_disconnect_chnl"} {:axiom} l2cu_disconnect_chnl(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj`p_lcb_o
    modifies csm`footprint
    ensures h_ccb.obj.local_cid() != old(h_ccb.obj.local_cid())
    ensures if (old(h_ccb.obj.local_cid()) >= L2CAP_BASE_APPL_CID)
            then && IsPeerDisconnectReqSent()
                 && csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendDisconnectReq]
            else csm.footprint == old(csm.footprint)
    ensures h_ccb.obj.IsDestroyed()

  method {:extern "stack_extern", "se_l2cu_send_peer_config_rsp"} {:axiom} l2cu_send_peer_config_rsp(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, cfg: ExternalHandle<ConfigAccessor>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConfigRspSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConfigRsp]

  method {:extern "stack_extern", "se_l2cu_send_credit_based_reconfig_req"} {:axiom} l2cu_send_credit_based_reconfig_req(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, le_cfg: ExternalHandle<ConfigAccessorLe>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConfigReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConfigReq]

  method {:extern "stack_extern", "se_l2cu_process_peer_cfg_req"} {:axiom} l2cu_process_peer_cfg_req(h_ccb: ExternalHandle<tL2C_CCB>, cfg: ExternalHandle<ConfigAccessor>) returns (res: uint8_t)
    // NOTE: This is overapproximating (the field may not necessarily change)
    ensures h_ccb.obj.peer_cfg_fcr_mode() != old(h_ccb.obj.peer_cfg_fcr_mode())

  method {:extern "stack_extern", "se_l2cu_process_peer_cfg_rsp"} {:axiom} l2cu_process_peer_cfg_rsp(h_ccb: ExternalHandle<tL2C_CCB>, cfg: ExternalHandle<ConfigAccessor>)
    modifies {}

  method {:extern "stack_extern", "se_l2c_link_adjust_allocation"} {:axiom} l2c_link_adjust_allocation()
    modifies {}

  method {:extern "stack_extern", "se_l2cu_process_our_cfg_req_and_send_peer"} {:axiom} l2cu_process_our_cfg_req_and_send_peer(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, cfg: ExternalHandle<ConfigAccessor>)
    // NOTE: This is overapproximating
    ensures h_ccb.obj.copy_our_cfg() != old(h_ccb.obj.copy_our_cfg())
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConfigReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConfigReq]

  method {:extern "stack_extern", "se_l2cu_process_our_cfg_req_and_send_peer_from_our_cfg"} {:axiom} l2cu_process_our_cfg_req_and_send_peer_from_our_cfg(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    // NOTE: This is overapproximating
    ensures h_ccb.obj.copy_our_cfg() != old(h_ccb.obj.copy_our_cfg())
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConfigReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConfigReq]

  method {:extern "stack_extern", "se_l2cu_process_our_cfg_rsp"} {:axiom} l2cu_process_our_cfg_rsp(h_ccb: ExternalHandle<tL2C_CCB>, cfg: ExternalHandle<ConfigAccessor>)
    ensures h_ccb.obj.our_cfg_fcr_mode() == old(h_ccb.obj.our_cfg_fcr_mode())
    ensures h_ccb.obj.peer_cfg_fcr_mode() == old(h_ccb.obj.peer_cfg_fcr_mode())
    ensures cfg.obj.copy() != old(cfg.obj.copy())

  // Security

  method {:extern "stack_extern", "se_l2ble_sec_access_req"} {:axiom} l2ble_sec_access_req(ghost csm: L2cCsm, bd_addr: RawAddress, psm: uint16_t, is_originator: bool, h_ccb: ExternalHandle<tL2C_CCB>) returns (result: tL2CAP_LE_RESULT_CODE)
    modifies csm`footprint
    ensures IsSecAccessReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.CheckSecurityRequirements]

  method {:extern "stack_extern", "se_btm_sec_l2cap_access_req"} {:axiom} btm_sec_l2cap_access_req(ghost csm: L2cCsm, bd_addr: RawAddress, psm: uint16_t, is_originator: bool, h_ccb: ExternalHandle<tL2C_CCB>) returns (result: tBTM_STATUS)
    modifies csm`footprint
    ensures IsSecAccessReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.CheckSecurityRequirements]

  method {:extern "stack_extern", "se_btm_sec_abort_access_req"} {:axiom} btm_sec_abort_access_req(ghost csm: L2cCsm, bd_addr: RawAddress)
    modifies csm`footprint
    ensures IsSecAbortReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.AbortSecAccessReq]

  // BLE

  method {:extern "stack_extern", "se_l2cble_credit_based_conn_req"} {:axiom} l2cble_credit_based_conn_req(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConnectReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectReq]

  method {:extern "stack_extern", "se_l2cble_credit_based_conn_res"} {:axiom} l2cble_credit_based_conn_res(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, result: uint16_t)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerConnectRspSent()
    ensures match result {
              case L2CAP_CONN_OK => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(ConnectRspResult.Success)]
              case _ => csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendConnectRsp(Refused)]
            }

  method {:extern "stack_extern", "se_l2cble_send_peer_disc_req"} {:axiom} l2cble_send_peer_disc_req(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o
    modifies csm`footprint
    ensures IsPeerDisconnectReqSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendDisconnectReq]

  method {:extern "stack_extern", "se_l2cble_send_flow_control_credit"} {:axiom} l2cble_send_flow_control_credit(h_ccb: ExternalHandle<tL2C_CCB>, credit: uint16_t)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o

  // FCR

  method {:extern "stack_extern", "se_l2c_fcr_proc_tout"} {:axiom} l2c_fcr_proc_tout(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
    modifies h_ccb.obj.p_lcb_o
    modifies h_ccb.obj.p_lcb_o
    ensures !(h_ccb.obj.peer_cfg_fcr_max_transmit() != 0
              && old(h_ccb.obj.fcrb_num_tries()) + 1 > h_ccb.obj.peer_cfg_fcr_max_transmit())
            ==> unchanged(h_ccb.obj`p_lcb_o)
    modifies csm`footprint
    requires h_ccb.obj.fcrb_num_tries() < UINT8_MAX
    ensures h_ccb.obj.fcrb_num_tries() == old(h_ccb.obj.fcrb_num_tries()) + 1
    ensures if h_ccb.obj.peer_cfg_fcr_max_transmit() != 0
               && h_ccb.obj.fcrb_num_tries() + 1 > h_ccb.obj.peer_cfg_fcr_max_transmit()
               && h_ccb.obj.local_cid() >= L2CAP_BASE_APPL_CID
            then && IsPeerDisconnectReqSent()
                 && csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendDisconnectReq]
            else csm.footprint == old(csm.footprint)

  method {:extern "stack_extern", "se_l2c_fcr_start_timer"} {:axiom} l2c_fcr_start_timer(h_ccb: ExternalHandle<tL2C_CCB>)

  method {:extern "stack_extern", "se_l2c_fcr_adj_monitor_retran_timeout"} {:axiom} l2c_fcr_adj_monitor_retran_timeout(h_ccb: ExternalHandle<tL2C_CCB>)

  method {:extern "stack_extern", "se_l2c_fcr_proc_ack_tout" } {:axiom} l2c_fcr_proc_ack_tout(h_ccb: ExternalHandle<tL2C_CCB>)
    requires h_ccb.obj.p_lcb_o != null
    modifies h_ccb.obj.p_lcb_o

  method {:extern "stack_extern", "se_l2c_fcr_chk_chan_modes"} {:axiom} l2c_fcr_chk_chan_modes(h_ccb: ExternalHandle<tL2C_CCB>) returns (compatible: bool)
    requires h_ccb.obj.p_lcb_o != null
    ensures compatible == !l2c_csm_incompatible_channels(h_ccb.obj)
    ensures !compatible ==> h_ccb.obj.rcb_ertm_info_preferred_mode() == 0

  // CSM
  method {:extern "stack_extern", "se_l2c_enqueue_peer_data"} {:axiom} l2c_enqueue_peer_data(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, p_data: NativeHandle<BT_HDR>)
    // TODO: Not sure if there are further modifications
    modifies csm`footprint
    ensures IsDataSent()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.SendData]

  // Alarm

  // Sets an |alarm| to execute a callback in the main message loop. This function
  // is same as |alarm_set| except that the |cb| callback is scheduled for
  // execution in the context of the main message loop.
  method {:extern "stack_extern", "se_alarm_set_on_mloop"} {:axiom} alarm_set_on_mloop(h_ccb: ExternalHandle<tL2C_CCB>, interval_ms : uint64_t)

  // This function cancels the |alarm| if it was previously set.
  // When this call returns, the caller has a guarantee that the
  // callback is not in progress and will not be called if it
  // hasn't already been called. This function is idempotent.
  // |alarm| may not be NULL.
  method {:extern "stack_extern", "se_alarm_cancel"} {:axiom} alarm_cancel(h_ccb: ExternalHandle<tL2C_CCB>)

  method {:extern "stack_extern", "se_alarm_cancel_lcb"} {:axiom} alarm_cancel_lcb(h_lcb: ExternalHandle<tL2C_LCB>)

  method {:extern "stack_extern", "se_BTM_SetLinkPolicyActiveMode"} {:axiom} BTM_SetLinkPolicyActiveMode(remote_bda : RawAddress) returns (success: bool)

  // ACL
  method {:extern "stack_extern", "se_acl_disconnect_from_handle"} {:axiom} acl_disconnect_from_handle(h_ccb: ExternalHandle<tL2C_CCB>, reason: uint8_t)
    requires h_ccb.obj.p_lcb_o != null
    // FIXME: Not obvious why but it causes a weird complain from dafny
    // modifies h_ccb.obj.p_lcb_o
    // TODO: Not sure
    ensures h_ccb.obj.IsDestroyed()

  method {:extern "stack_extern", "se_btm_acl_notif_conn_collision"} {:axiom} btm_acl_notif_conn_collision(bda: RawAddress)

  method {:extern "stack_extern", "se_l2c_csm_osi_free"} {:axiom} l2c_csm_osi_free(data: IgnorableData)

  // Fixed Queue
  method {:extern "stack_extern", "se_xmit_hold_queue_is_empty"} {:axiom} xmit_hold_queue_is_empty(h_ccb: ExternalHandle<tL2C_CCB>) returns (res: bool)

  // Link
  method {:extern "stack_extern", "se_l2c_link_check_send_pkts_null"} {:axiom} l2c_link_check_send_pkts_null(h_lcb: ExternalHandle<tL2C_LCB>, local_cid: uint16_t)
    modifies h_lcb.obj

  module Helpers {
    // This group of functions do not exist as a function in the native code.
    // There are several reasons for their existence:
    // - Performing actions not relevant to the verification of the state machine.
    // - Performing an action that is not possible in Dafny.

    import opened ExternalTypes
    import opened AbsTypes
    import opened Types
    import opened OpaqueTypes

    import opened OpsStateMachine
    import opened L2cCsmOsm
    import opened Utils
      // Custom

    /* Special functions for credit-based connection */

    method {:extern "complexity_helpers", "ch_l2c_csm_open_credit_based_conn"} {:axiom} l2c_csm_open_credit_based_conn(h_ccb: ExternalHandle<tL2C_CCB>, h_ci: ExternalHandle<tL2C_CONN_INFO>)
      requires h_ccb.obj.p_lcb_o != null
      modifies h_ccb.obj.p_lcb_o
      modifies h_ccb.obj`chnl_state
      ensures h_ccb.obj.chnl_state == CST_OPEN

    // NOTE: !is_local will result in additional logging debug messages and sending error messages
    /*
     * LOG(WARNING) << __func__ << ": lcid= " << loghex(cid);
     * (*p_ccb->p_rcb->api.pL2CA_Error_Cb)(p_ccb->local_cid,
     *                                    L2CAP_CONN_TIMEOUT);
     */
    method {:extern "complexity_helpers", "ch_l2c_csm_close_credit_based_conn"} {:axiom} l2c_csm_close_credit_based_conn(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, is_local: bool)
      requires h_ccb.obj.p_lcb_o != null
      modifies h_ccb.obj.p_lcb_o
      // TODO: Not sure
      ensures h_ccb.obj.IsDestroyed()

    method {:extern "complexity_helpers", "ch_l2c_csm_close_config_conn"} {:axiom} l2c_csm_close_config_conn(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>)
      // May call release
      modifies h_ccb.obj`p_lcb_o
      // However, based on the implementation should not set lcb to null.
      ensures h_ccb.obj.p_lcb_o != null

    // Callback Calling

    method {:extern "complexity_helpers", "ch_l2c_csm_config_fixed_data_ind"} {:axiom} l2c_csm_config_fixed_data_ind(ghost csm: L2cCsm, h_ccb: ExternalHandle<tL2C_CCB>, p_data: NativeHandle<BT_HDR>)
      modifies csm`footprint
      ensures IsPDUProcessed()
      ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.ProcessPDU]

    method {:extern "complexity_helpers", "ch_l2c_csm_indicate_credit_based_connection_open"} {:axiom} l2c_csm_indicate_credit_based_connection_open(h_ccb: ExternalHandle<tL2C_CCB>)

    // Exists in CSM
    method {:extern "complexity_helpers", "ch_l2c_csm_indicate_connection_open"} {:axiom} l2c_csm_indicate_connection_open(h_ccb: ExternalHandle<tL2C_CCB>)

    method {:extern "complexity_helpers", "ch_l2c_csm_send_config_req_set_and_get_our_cfg"} {:axiom} l2c_csm_send_config_req_set_and_get_our_cfg(h_ccb: ExternalHandle<tL2C_CCB>) returns (cfg: ConfigAccessor)
      ensures h_ccb.obj.copy_our_cfg() == cfg.copy()

    method {:extern "complexity_helpers", "ch_l2c_csm_send_config_rsp_ok_get_cfg"} {:axiom} l2c_csm_send_config_rsp_ok_get_cfg() returns (cfg: ConfigAccessor)
  }
}
