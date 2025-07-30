module Impl.Types {
  import TypeAliases
  import opened AbsTypes
  import opened ExternalTypes
  import opened CommonExtern
  import opened CommonTypes
  import OpaqueTypes
  import L2cCsmOsm
  import OpsStateMachine

  type uint8_t = TypeAliases.uint8_t
  type uint16_t = TypeAliases.uint16_t
  type uint32_t = TypeAliases.uint32_t
  type uint64_t = TypeAliases.uint64_t

  type tBTM_STATUS = uint8_t
  type tL2CAP_LE_RESULT_CODE = uint8_t

  type RawAddress = OpaqueTypes.RawAddress
  type BT_HDR = OpaqueTypes.BT_HDR
  type IgnorableData = OpaqueTypes.IgnorableData
  type ExeCheckpoint = OpaqueTypes.ExeCheckpoint

  datatype ChannelState =
      CST_CLOSED
    | CST_ORIG_W4_SEC_COMP
    | CST_TERM_W4_SEC_COMP
    | CST_W4_L2CAP_CONNECT_RSP
    | CST_W4_L2CA_CONNECT_RSP
    | CST_CONFIG
    | CST_OPEN
    | CST_W4_L2CAP_DISCONNECT_RSP
    | CST_W4_L2CA_DISCONNECT_RSP

  type tL2C_CHNL_STATE = ChannelState

  type tL2C_CCB_NativeHandle = NativeHandle<ChannelControlBlock>

  class ChannelControlBlock {
    var handle: tL2C_CCB_NativeHandle
    var chnl_state : ChannelState
    var peer_conn_cfg : LeConfigInfo
    var remote_cid : uint16_t
    var config_done : bv8
    var remote_config_rsp_result : uint16_t
    var flags : bv8
    var fcr_cfg_tries : uint8_t
    var p_lcb_o : LinkControlBlock?
    ghost var destroy_handle: bool
    ghost var external_event: Option<tL2CEVT>

    constructor(handle: tL2C_CCB_NativeHandle, chnl_state : ChannelState, peer_conn_cfg : LeConfigInfo, remote_cid : uint16_t, config_done : bv8, remote_config_rsp_result : uint16_t, flags : bv8, fcr_cfg_tries : uint8_t, p_lcb_o : LinkControlBlock?)
      ensures this.handle == handle
      ensures this.chnl_state == chnl_state
      ensures this.peer_conn_cfg == peer_conn_cfg
      ensures this.remote_cid == remote_cid
      ensures this.config_done == config_done
      ensures this.remote_config_rsp_result == remote_config_rsp_result
      ensures this.flags == flags
      ensures this.fcr_cfg_tries == fcr_cfg_tries
      ensures this.p_lcb_o == p_lcb_o
    {
      this.handle := handle;
      this.chnl_state := chnl_state;
      this.peer_conn_cfg := peer_conn_cfg;
      this.remote_cid := remote_cid;
      this.config_done := config_done;
      this.remote_config_rsp_result := remote_config_rsp_result;
      this.flags := flags;
      this.fcr_cfg_tries := fcr_cfg_tries;
      this.p_lcb_o := p_lcb_o;
    }

    function GetExternalHandle() : (handle: ExternalHandle <ChannelControlBlock>)
      ensures handle.obj == this
    {
      NewExternalHandle(this)
    }

    ghost predicate IsInState(state: ChannelState)
      reads this`chnl_state, this`handle, this`destroy_handle
    {
      this.chnl_state == state && !this.IsDestroyed()
    }

    function IsDestroyed(): bool
      reads this`handle
      reads this`destroy_handle
    {
      is_ccb_destroyed(GetExternalHandle())
    }

    function ExeCheckpoint(): ExeCheckpoint
      reads this`handle
    {
      CCB_exe_checkpoint(GetExternalHandle())
    }

    function MaybeSingleEventSince(checkpoint: ExeCheckpoint) : Option<tL2CEVT>
      reads this`handle
    {
      CCB_maybe_single_event_since(GetExternalHandle(), checkpoint)
    }

    function local_cid() : uint16_t
      reads this`handle
    {
      CCB_local_cid(GetExternalHandle())
    }

    function remote_id() : uint8_t
      reads this`handle
    {
      CCB_remote_id(GetExternalHandle())
    }

    function connection_initiator() : bool
      reads this`handle
    {
      CCB_connection_initiator(GetExternalHandle())
    }

    function ecoc() : bool
      reads this`handle
    {
      CCB_ecoc(GetExternalHandle())
    }

    function fcrb_num_tries() : uint8_t
      reads this`handle
    {
      CCB_fcrb_num_tries(GetExternalHandle())
    }

    function fcrb_wait_ack() : bool
      reads this`handle
    {
      CCB_fcrb_wait_ack(GetExternalHandle())
    }

    function rcb_psm() : uint16_t
      reads this`handle
    {
      CCB_rcb_psm(GetExternalHandle())
    }

    function rcb_ertm_info_preferred_mode() : uint8_t
      reads this`handle
    {
      CCB_rcb_ertm_info_preferred_mode(GetExternalHandle())
    }

    function rcb_coc_cfg_credits() : uint16_t
      reads this`handle
    {
      CCB_rcb_coc_cfg_credits(GetExternalHandle())
    }

    function our_cfg_fcr_mode(): uint8_t
      reads this`handle
    {
      CCB_our_cfg_fcr_mode(GetExternalHandle())
    }

    function copy_our_cfg(): ConfigInfo
      reads this`handle
    {
      CCB_copy_our_cfg(GetExternalHandle())
    }

    method update_our_cfg(our_cfg: ConfigInfo)
      ensures this.copy_our_cfg() == our_cfg
    {
      CCB_update_our_cfg(GetExternalHandle(), our_cfg);
    }

    function peer_cfg_fcr_mode(): uint8_t
      reads this`handle
    {
      CCB_peer_cfg_fcr_mode(GetExternalHandle())
    }

    function peer_cfg_fcr_max_transmit(): uint8_t
      reads this`handle
    {
      CCB_peer_cfg_fcr_max_transmit(GetExternalHandle())
    }

    method clear_cached_peer_cfg()
    {
      CCB_clear_cached_peer_cfg(GetExternalHandle());
    }

    method remove_timeout_if_only_channel()
      modifies this`p_lcb_o
    {
      CCB_remove_timeout_if_only_channel(GetExternalHandle());
    }

    method init_le_coc_configs()
      requires this.p_lcb_o != null && this.p_lcb_o.is_ble()
      requires this.chnl_state == CST_OPEN
    {
      CCB_init_le_coc_configs(GetExternalHandle());
    }

    method invoke_ConfigInd(cfg: ConfigAccessor)
    {
      CCB_callback_ConfigInd(GetExternalHandle(), cfg.GetExternalHandle());
    }

    method invoke_DisconnectInd(should_ack: bool)
      modifies this`external_event
      modifies this`destroy_handle
      // L2CA_DisconnectReq may get called by this callback which executes the following event.
      ensures old(this.IsDestroyed()) ==> this.external_event.None?
      ensures this.external_event.None? || this.external_event.value == L2CEVT_L2CA_DISCONNECT_REQ
      ensures (!old(this.IsDestroyed()) && this.IsDestroyed()) ==> this.external_event.Some?
    {
      var exe_checkpoint := this.ExeCheckpoint();
      var is_destroyed_before := this.IsDestroyed();

      CCB_callback_DisconnectInd(GetExternalHandle(), should_ack);

      var executed_event := this.MaybeSingleEventSince(exe_checkpoint);
      this.external_event := executed_event;
      if is_destroyed_before {
        RuntimeAssert(executed_event.None?);
      } else {
        RuntimeAssert(executed_event.None? || executed_event.value == L2CEVT_L2CA_DISCONNECT_REQ);
        if this.IsDestroyed() {
          RuntimeAssert(executed_event.Some?);
        }
      }
    }

    method invoke_DataIndWithMetrics(ghost csm: L2cCsmOsm.L2cCsm, p_buff: NativeHandle<BT_HDR>)
      modifies csm`footprint
      ensures L2cCsmOsm.IsPDUProcessed()
      ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.ProcessPDU]
    {
      CCB_callback_DataIndWithMetrics(csm, GetExternalHandle(), p_buff);
    }

    method invoke_Error(error_code: uint16_t)
    {
      CCB_callback_Error(GetExternalHandle(), error_code);
    }

    method invoke_CreditBasedConnectCfm(peer_mtu: uint16_t, result: uint16_t)
    {
      CCB_callback_CreditBasedConnectCfm(GetExternalHandle(), peer_mtu, result);
    }

    method invoke_CreditBasedReconfigCompleted(is_local_cfg: bool, le_cfg: ExternalHandle<ConfigAccessorLe>)
    {
      CCB_callback_CreditBasedReconfigCompleted(GetExternalHandle(), is_local_cfg, le_cfg);
    }
  }

  type tL2C_CCB = ChannelControlBlock
  type tL2C_CCB? = ChannelControlBlock?

  type tL2C_LCB_NativeHandle = NativeHandle<LinkControlBlock>

  class LinkControlBlock {
    var handle: tL2C_LCB_NativeHandle
    constructor(handle: tL2C_LCB_NativeHandle)
      ensures this.handle == handle
    {
      this.handle := handle;
    }

    function GetExternalHandle() : (handle: ExternalHandle <LinkControlBlock>)
      ensures handle.obj == this
    {
      NewExternalHandle(this)
    }

    function remote_bd_addr() : RawAddress
      reads this`handle
    {
      LCB_remote_bd_addr(GetExternalHandle())
    }

    function w4_info_rsp() : bool
      reads this`handle
    {
      LCB_w4_info_rsp(GetExternalHandle())
    }

    function peer_ext_fea() : uint32_t
      reads this`handle
    {
      LCB_peer_ext_fea(GetExternalHandle())
    }

    function is_ble() : bool
      reads this`handle
    {
      LCB_is_ble(GetExternalHandle())
    }

    function pending_ecoc_conn_cnt() : uint8_t
      reads this`handle
    {
      LCB_pending_ecoc_conn_cnt(GetExternalHandle())
    }
  }

  type tL2C_LCB = LinkControlBlock
  type tL2C_LCB? = LinkControlBlock?


  type tL2CAP_CFG_INFO_NativeHandle = NativeHandle<ConfigAccessor>
  class ConfigAccessor {
    var handle: tL2CAP_CFG_INFO_NativeHandle

    constructor(handle: tL2CAP_CFG_INFO_NativeHandle)
      ensures this.handle == handle
    {
      this.handle := handle;
    }

    function GetExternalHandle() : (handle: ExternalHandle <ConfigAccessor>)
      ensures handle.obj == this
    {
      NewExternalHandle(this)
    }

    function flags(): uint16_t
      reads this`handle
    {
      CFG_flags(this.handle)
    }

    // TODO: Add a flag to guarantee that modifications are written back.
    function copy(): ConfigInfo
      reads this`handle
    {
      CFG_copy(this.handle)
    }

    // TODO: Add a flag to guarantee that modifications are written back.
    method update(cfg: ConfigInfo)
      ensures this.copy() == cfg
    {
      CFG_update(this.handle, cfg);
    }
  }

  type tL2CAP_LE_CFG_INFO_NativeHandle = NativeHandle<ConfigAccessorLe>
  class ConfigAccessorLe {
    var handle: tL2CAP_LE_CFG_INFO_NativeHandle

    constructor(handle: tL2CAP_LE_CFG_INFO_NativeHandle)
      ensures this.handle == handle
    {
      this.handle := handle;
    }

    function GetExternalHandle() : (handle: ExternalHandle <ConfigAccessorLe>)
      ensures handle.obj == this
    {
      NewExternalHandle(this)
    }
  }

  datatype CsmEvent =
      L2CEVT_LP_CONNECT_CFM
    | L2CEVT_LP_CONNECT_CFM_NEG
    | L2CEVT_LP_CONNECT_IND
    | L2CEVT_LP_DISCONNECT_IND
    | L2CEVT_SEC_COMP
    | L2CEVT_SEC_COMP_NEG
    | L2CEVT_L2CAP_CONNECT_REQ
    | L2CEVT_L2CAP_CONNECT_RSP
    | L2CEVT_L2CAP_CONNECT_RSP_PND
    | L2CEVT_L2CAP_CONNECT_RSP_NEG
    | L2CEVT_L2CAP_CONFIG_REQ
    | L2CEVT_L2CAP_CONFIG_RSP
    | L2CEVT_L2CAP_CONFIG_RSP_NEG
    | L2CEVT_L2CAP_DISCONNECT_REQ
    | L2CEVT_L2CAP_DISCONNECT_RSP
    | L2CEVT_L2CAP_INFO_RSP /* Peer information response */
    | L2CEVT_L2CAP_DATA
    | L2CEVT_L2CA_CONNECT_REQ
    | L2CEVT_L2CA_CONNECT_RSP
    | L2CEVT_L2CA_CONNECT_RSP_NEG
    | L2CEVT_L2CA_CONFIG_REQ
    | L2CEVT_L2CA_CONFIG_RSP
    | L2CEVT_L2CA_DISCONNECT_REQ
    | L2CEVT_L2CA_DISCONNECT_RSP
    | L2CEVT_L2CA_DATA_READ
    | L2CEVT_L2CA_DATA_WRITE
    | L2CEVT_TIMEOUT
    | L2CEVT_SEC_RE_SEND_CMD
    | L2CEVT_ACK_TIMEOUT
    | L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT
    | L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT
    | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ
    | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP
    | L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG
    | L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ
    | L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP
    | L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ
    | L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP
    | L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG
    | L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ
      // custom events to handle secutiry access check results
    | L2CEVT_SEC_ACCESS
    | L2CEVT_SEC_ACCESS_PND
    | L2CEVT_SEC_ACCESS_NEG
      // custom events to handle various transitions in Config state
    | L2CEVT_L2CA_RECONFIG_RSP
    | L2CEVT_L2CA_CONFIG_RSP_NEG
    | L2CEVT_L2CA_RECONFIG_REQ
  type tL2CEVT = CsmEvent

  class ConnectionInfo {
    var handle: NativeHandle<ConnectionInfo>
    constructor(handle: NativeHandle<ConnectionInfo>)
    {
      this.handle := handle;
    }

    function GetExternalHandle() : (handle: ExternalHandle<ConnectionInfo>)
      ensures handle.obj == this
    {
      NewExternalHandle(this)
    }

    function status(): uint8_t
      reads this`handle
    {
      CI_status(this.GetExternalHandle())
    }

    function l2cap_result(): uint16_t
      reads this`handle
    {
      CI_l2cap_result(this.GetExternalHandle())
    }

    function l2cap_status(): uint16_t
      reads this`handle
    {
      CI_l2cap_status(this.GetExternalHandle())
    }

    function remote_cid(): uint16_t
      reads this`handle
    {
      CI_remote_cid(this.GetExternalHandle())
    }

    function peer_mtu(): uint16_t
      reads this`handle
    {
      CI_peer_mtu(this.GetExternalHandle())
    }
  }

  type tL2C_CONN_INFO = ConnectionInfo
  type tL2C_CONN_INFO? = ConnectionInfo?

  datatype FcrOptions = FcrOptions (
    mode : uint8_t,
    rtrans_tout : uint16_t,
    mon_tout : uint16_t
  )



  datatype ConfigInfo = tL2CAP_CFG_INFO (
    result : uint16_t,
    mtu_present : bool,
    mtu : uint16_t,
    fcr_present : bool,
    fcr : FcrOptions,
    ext_flow_spec_present : bool
  )

  const L2CAP_LE_CREDIT_MAX : uint16_t := 65535

  datatype LeConfigInfo = LeConfigInfo (
    credits : uint16_t
  )

  const L2CAP_INITIATOR_LOCAL : uint16_t := 1

  function {:extern "complexity_helpers", "ch_is_ccb_destroyed"} is_ccb_destroyed(h_ccb: ExternalHandle<ChannelControlBlock>): bool
    reads h_ccb.obj`destroy_handle
  function {:extern "ptr_getters", "CCB_exe_checkpoint"} CCB_exe_checkpoint(ccb: ExternalHandle<ChannelControlBlock>): ExeCheckpoint
  function {:extern "complexity_helpers", "ch_CCB_maybe_single_event_since"} CCB_maybe_single_event_since(ccb: ExternalHandle<ChannelControlBlock>, checkpoint: ExeCheckpoint): Option<tL2CEVT>

  function {:extern "ptr_getters", "CCB_local_cid"} CCB_local_cid(ccb: ExternalHandle<ChannelControlBlock>): uint16_t
  function {:extern "ptr_getters", "CCB_remote_id"} CCB_remote_id(ccb: ExternalHandle<ChannelControlBlock>): uint8_t
  function {:extern "ptr_getters", "CCB_connection_initiator"} CCB_connection_initiator(ccb: ExternalHandle<ChannelControlBlock>): bool
  function {:extern "ptr_getters", "CCB_ecoc"} CCB_ecoc(ccb: ExternalHandle<ChannelControlBlock>): bool
  function {:extern "ptr_getters", "CCB_fcrb_num_tries"} CCB_fcrb_num_tries(ccb: ExternalHandle<ChannelControlBlock>): uint8_t
  function {:extern "ptr_getters", "CCB_fcrb_wait_ack"} CCB_fcrb_wait_ack(ccb: ExternalHandle<ChannelControlBlock>): bool
  function {:extern "ptr_getters", "CCB_rcb_psm"} CCB_rcb_psm(ccb: ExternalHandle<ChannelControlBlock>): uint16_t
  function {:extern "ptr_getters", "CCB_rcb_ertm_info_preferred_mode"} CCB_rcb_ertm_info_preferred_mode(ccb: ExternalHandle<ChannelControlBlock>): uint8_t
  function {:extern "ptr_getters", "CCB_rcb_coc_cfg_credits"} CCB_rcb_coc_cfg_credits(ccb: ExternalHandle<ChannelControlBlock>): uint16_t
  function {:extern "ptr_getters", "CCB_our_cfg_fcr_mode"} CCB_our_cfg_fcr_mode(ccb: ExternalHandle<ChannelControlBlock>): uint8_t
  function {:extern "ptr_getters", "CCB_copy_our_cfg"} {:axiom} CCB_copy_our_cfg(ccb: ExternalHandle<ChannelControlBlock>): ConfigInfo
    ensures
      CCB_our_cfg_fcr_mode(ccb) == CCB_copy_our_cfg(ccb).fcr.mode
  function {:extern "ptr_getters", "CCB_peer_cfg_fcr_mode"} CCB_peer_cfg_fcr_mode(ccb: ExternalHandle<ChannelControlBlock>): uint8_t
  function {:extern "ptr_getters", "CCB_peer_cfg_fcr_max_transmit"} CCB_peer_cfg_fcr_max_transmit(ccb: ExternalHandle<ChannelControlBlock>): uint8_t

  method {:extern "ptr_setters", "CCB_update_our_cfg"} {:axiom} CCB_update_our_cfg(ccb: ExternalHandle<ChannelControlBlock>, our_cfg: ConfigInfo)
    ensures
      CCB_copy_our_cfg(ccb) == our_cfg
  method {:extern "ptr_setters", "CCB_clear_cached_peer_cfg"} CCB_clear_cached_peer_cfg(ccb: ExternalHandle<ChannelControlBlock>)
  method {:extern "ptr_setters", "CCB_remove_timeout_if_only_channel"} CCB_remove_timeout_if_only_channel(ccb: ExternalHandle<ChannelControlBlock>)
  method {:extern "ptr_setters", "CCB_init_le_coc_configs"} CCB_init_le_coc_configs(ccb: ExternalHandle<ChannelControlBlock>)

  method {:extern "cb_callers", "CCB_callback_ConfigInd"} CCB_callback_ConfigInd(ccb: ExternalHandle<ChannelControlBlock>, cfg: ExternalHandle<ConfigAccessor>)
  method {:extern "cb_callers", "CCB_callback_DisconnectInd"} {:axiom} CCB_callback_DisconnectInd(ccb: ExternalHandle<ChannelControlBlock>, should_ack: bool)
    modifies ccb.obj`destroy_handle
  method {:extern "cb_callers", "CCB_callback_DataInd_with_metrics"} {:axiom} CCB_callback_DataIndWithMetrics(ghost csm: L2cCsmOsm.L2cCsm, ccb: ExternalHandle<ChannelControlBlock>, p_buff: NativeHandle<BT_HDR>)
    modifies csm`footprint
    ensures L2cCsmOsm.IsPDUProcessed()
    ensures csm.footprint == old(csm.footprint) + [L2cCsmOsm.ProcessPDU]
  method {:extern "cb_callers", "CCB_callback_Error"} CCB_callback_Error(ccb: ExternalHandle<ChannelControlBlock>, error_code: uint16_t)
  method {:extern "cb_callers", "CCB_callback_CreditBasedConnectCfm"} CCB_callback_CreditBasedConnectCfm(ccb: ExternalHandle<ChannelControlBlock>, peer_mtu: uint16_t, result: uint16_t)
  method {:extern "cb_callers", "CCB_callback_CreditBasedReconfigCompleted"} CCB_callback_CreditBasedReconfigCompleted(ccb: ExternalHandle<ChannelControlBlock>, is_local_cfg: bool, le_cfg: ExternalHandle<ConfigAccessorLe>)

  function {:extern "ptr_getters", "LCB_remote_bd_addr"} LCB_remote_bd_addr(lcb: ExternalHandle<LinkControlBlock>): RawAddress
  function {:extern "ptr_getters", "LCB_w4_info_rsp"} LCB_w4_info_rsp(lcb: ExternalHandle<LinkControlBlock>): bool
  function {:extern "ptr_getters", "LCB_peer_ext_fea"} LCB_peer_ext_fea(lcb: ExternalHandle<LinkControlBlock>): uint32_t
  function {:extern "ptr_getters", "LCB_is_ble"} LCB_is_ble(lcb: ExternalHandle<LinkControlBlock>): bool
  function {:extern "ptr_getters", "LCB_pending_ecoc_conn_cnt"} LCB_pending_ecoc_conn_cnt(lcb: ExternalHandle<LinkControlBlock>): uint8_t

  function {:extern "ptr_getters", "CFG_flags"} CFG_flags(handle: tL2CAP_CFG_INFO_NativeHandle): uint16_t
  function {:extern "ptr_getters", "CFG_copy"} CFG_copy(handle: tL2CAP_CFG_INFO_NativeHandle): ConfigInfo
  method {:extern "ptr_setters", "CFG_update"} {:axiom} CFG_update(handle: tL2CAP_CFG_INFO_NativeHandle, cfg: ConfigInfo)
    ensures CFG_copy(handle) == cfg

  function {:extern "ptr_getters", "CI_status"} CI_status(ccb: ExternalHandle<ConnectionInfo>): uint8_t
  function {:extern "ptr_getters", "CI_l2cap_result"} CI_l2cap_result(ccb: ExternalHandle<ConnectionInfo>): uint16_t
  function {:extern "ptr_getters", "CI_l2cap_status"} CI_l2cap_status(ccb: ExternalHandle<ConnectionInfo>): uint16_t
  function {:extern "ptr_getters", "CI_remote_cid"} CI_remote_cid(ccb: ExternalHandle<ConnectionInfo>): uint16_t
  function {:extern "ptr_getters", "CI_peer_mtu"} CI_peer_mtu(ccb: ExternalHandle<ConnectionInfo>): uint16_t
}