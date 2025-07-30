module Impl.Utils {
  import opened Types
  import opened External.Logging

  import opened OpsStateMachine

  ghost function l2c_csm_connection_mode(p_ccb: tL2C_CCB): ConnectionMode
    requires p_ccb.p_lcb_o != null
    reads p_ccb, p_ccb.p_lcb_o
  {
    if p_ccb.p_lcb_o.is_ble()
    then Ble
    else Classic
  }

  ghost predicate l2c_csm_incompatible_channels(p_ccb: tL2C_CCB)

  function l2c_csm_get_event_name(event: tL2CEVT): string {
    match event {
      case L2CEVT_LP_CONNECT_CFM => "LOWER_LAYER_CONNECT_CFM"
      case L2CEVT_LP_CONNECT_CFM_NEG => "LOWER_LAYER_CONNECT_CFM_NEG"
      case L2CEVT_LP_CONNECT_IND => "LOWER_LAYER_CONNECT_IND"
      case L2CEVT_LP_DISCONNECT_IND => "LOWER_LAYER_DISCONNECT_IND"

      case L2CEVT_SEC_COMP => "SECURITY_COMPLETE"
      case L2CEVT_SEC_COMP_NEG => "SECURITY_COMPLETE_NEG"

      case L2CEVT_L2CAP_CONNECT_REQ => "PEER_CONNECT_REQ"
      case L2CEVT_L2CAP_CONNECT_RSP => "PEER_CONNECT_RSP"
      case L2CEVT_L2CAP_CONNECT_RSP_PND => "PEER_CONNECT_RSP_PND"
      case L2CEVT_L2CAP_CONNECT_RSP_NEG => "PEER_CONNECT_RSP_NEG"
      case L2CEVT_L2CAP_CONFIG_REQ => "PEER_CONFIG_REQ"
      case L2CEVT_L2CAP_CONFIG_RSP => "PEER_CONFIG_RSP"
      case L2CEVT_L2CAP_CONFIG_RSP_NEG => "PEER_CONFIG_RSP_NEG"
      case L2CEVT_L2CAP_DISCONNECT_REQ => "PEER_DISCONNECT_REQ"
      case L2CEVT_L2CAP_DISCONNECT_RSP => "PEER_DISCONNECT_RSP"
      case L2CEVT_L2CAP_DATA => "PEER_DATA"

      case L2CEVT_L2CA_CONNECT_REQ => "UPPER_LAYER_CONNECT_REQ"
      case L2CEVT_L2CA_CONNECT_RSP => "UPPER_LAYER_CONNECT_RSP"
      case L2CEVT_L2CA_CONNECT_RSP_NEG => "UPPER_LAYER_CONNECT_RSP_NEG"
      case L2CEVT_L2CA_CONFIG_REQ => "UPPER_LAYER_CONFIG_REQ"
      case L2CEVT_L2CA_CONFIG_RSP => "UPPER_LAYER_CONFIG_RSP"
      case L2CEVT_L2CA_DISCONNECT_REQ => "UPPER_LAYER_DISCONNECT_REQ"
      case L2CEVT_L2CA_DISCONNECT_RSP => "UPPER_LAYER_DISCONNECT_RSP"
      case L2CEVT_L2CA_DATA_READ => "UPPER_LAYER_DATA_READ"
      case L2CEVT_L2CA_DATA_WRITE => "UPPER_LAYER_DATA_WRITE"

      case L2CEVT_TIMEOUT => "TIMEOUT"
      case L2CEVT_SEC_RE_SEND_CMD => "SEC_RE_SEND_CMD"
      case L2CEVT_L2CAP_INFO_RSP => "L2CEVT_L2CAP_INFO_RSP"
      case L2CEVT_ACK_TIMEOUT => "L2CEVT_ACK_TIMEOUT"

      case L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT => "SEND_FLOW_CONTROL_CREDIT"
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ => "SEND_CREDIT_BASED_CONNECT_REQ"
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP => "SEND_CREDIT_BASED_CONNECT_RSP"
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG => "SEND_CREDIT_BASED_CONNECT_RSP_NEG"
      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ => "SEND_CREDIT_BASED_RECONFIG_REQ"

      case L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT => "RECV_FLOW_CONTROL_CREDIT"
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ => "RECV_CREDIT_BASED_CONNECT_REQ"
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP => "RECV_CREDIT_BASED_CONNECT_RSP"
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG => "RECV_CREDIT_BASED_CONNECT_RSP_NEG"
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ => "RECV_CREDIT_BASED_RECONFIG_REQ"
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP => "RECV_CREDIT_BASED_RECONFIG_RSP"

      case L2CEVT_SEC_ACCESS => "SECURITY_ACCESS"
      case L2CEVT_SEC_ACCESS_PND => "SECURITY_ACCESS_PND"
      case L2CEVT_SEC_ACCESS_NEG => "SECURITY_ACCESS_NEG"
      case L2CEVT_L2CA_RECONFIG_RSP => "RECONFIG_RSP"
      case L2CEVT_L2CA_CONFIG_RSP_NEG => "CONFIG_RSP_NEG"
      case L2CEVT_L2CA_RECONFIG_REQ => "RECONFIG_REQ"
    }
  }

  function l2c_csm_get_event_order(event: tL2CEVT): uint16_t {match event{
      case L2CEVT_LP_CONNECT_CFM => 0
      case L2CEVT_LP_CONNECT_CFM_NEG => 1
      case L2CEVT_LP_CONNECT_IND => 2
      case L2CEVT_LP_DISCONNECT_IND => 3


      case L2CEVT_SEC_COMP => 7
      case L2CEVT_SEC_COMP_NEG => 8


      case L2CEVT_L2CAP_CONNECT_REQ => 10
      case L2CEVT_L2CAP_CONNECT_RSP => 11
      case L2CEVT_L2CAP_CONNECT_RSP_PND => 12
      case L2CEVT_L2CAP_CONNECT_RSP_NEG => 13


      case L2CEVT_L2CAP_CONFIG_REQ => 14
      case L2CEVT_L2CAP_CONFIG_RSP => 15
      case L2CEVT_L2CAP_CONFIG_RSP_NEG => 16

      case L2CEVT_L2CAP_DISCONNECT_REQ => 17
      case L2CEVT_L2CAP_DISCONNECT_RSP => 18
      case L2CEVT_L2CAP_INFO_RSP => 19
      case L2CEVT_L2CAP_DATA => 20


      case L2CEVT_L2CA_CONNECT_REQ => 21
      case L2CEVT_L2CA_CONNECT_RSP => 22
      case L2CEVT_L2CA_CONNECT_RSP_NEG => 23
      case L2CEVT_L2CA_CONFIG_REQ => 24
      case L2CEVT_L2CA_CONFIG_RSP => 25
      case L2CEVT_L2CA_DISCONNECT_REQ => 27
      case L2CEVT_L2CA_DISCONNECT_RSP => 28
      case L2CEVT_L2CA_DATA_READ => 29
      case L2CEVT_L2CA_DATA_WRITE => 30

      case L2CEVT_TIMEOUT => 32
      case L2CEVT_SEC_RE_SEND_CMD => 33

      case L2CEVT_ACK_TIMEOUT => 34

      case L2CEVT_L2CA_SEND_FLOW_CONTROL_CREDIT => 35

      case L2CEVT_L2CAP_RECV_FLOW_CONTROL_CREDIT => 36
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_REQ =>        37
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP =>        38
      case L2CEVT_L2CAP_CREDIT_BASED_CONNECT_RSP_NEG =>        39
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_REQ =>        40
      case L2CEVT_L2CAP_CREDIT_BASED_RECONFIG_RSP =>        41


      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_REQ => 42
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP => 43
      case L2CEVT_L2CA_CREDIT_BASED_CONNECT_RSP_NEG => 44
      case L2CEVT_L2CA_CREDIT_BASED_RECONFIG_REQ => 45

      case L2CEVT_SEC_ACCESS => 46
      case L2CEVT_SEC_ACCESS_PND => 47
      case L2CEVT_SEC_ACCESS_NEG => 48
      case L2CEVT_L2CA_RECONFIG_RSP => 49
      case L2CEVT_L2CA_CONFIG_RSP_NEG => 50
      case L2CEVT_L2CA_RECONFIG_REQ => 51
    }}

  function l2c_csm_get_state_name(state: ChannelState): string {
    match state {
      case CST_CLOSED => "CLOSED"
      case CST_ORIG_W4_SEC_COMP => "ORIG_W4_SEC_COMP"
      case CST_TERM_W4_SEC_COMP => "TERM_W4_SEC_COMP"
      case CST_W4_L2CAP_CONNECT_RSP => "W4_L2CAP_CONNECT_RSP"
      case CST_W4_L2CA_CONNECT_RSP => "W4_L2CA_CONNECT_RSP"
      case CST_CONFIG => "CONFIG"
      case CST_OPEN => "OPEN"
      case CST_W4_L2CAP_DISCONNECT_RSP => "W4_L2CAP_DISCONNECT_RSP"
      case CST_W4_L2CA_DISCONNECT_RSP => "W4_L2CA_DISCONNECT_RSP"
    }
  }

  function l2c_csm_get_state_order(state: ChannelState): uint8_t {
    match state {
      case CST_CLOSED => 0
      case CST_ORIG_W4_SEC_COMP => 1
      case CST_TERM_W4_SEC_COMP => 2
      case CST_W4_L2CAP_CONNECT_RSP => 3
      case CST_W4_L2CA_CONNECT_RSP => 4
      case CST_CONFIG => 5
      case CST_OPEN => 6
      case CST_W4_L2CAP_DISCONNECT_RSP => 7
      case CST_W4_L2CA_DISCONNECT_RSP => 8
    }
  }


  method log_csm_execution_start(loc: string, state: ChannelState, event: tL2CEVT, p_ccb: tL2C_CCB) {
    if !is_logging_enabled() {
      return;
    }
    log_csm_execution_start_prefix(loc, "", state, event, p_ccb);
  }

  method log_csm_execution_start_prefix(loc: string, prefix: string, state: ChannelState, event: tL2CEVT, p_ccb: tL2C_CCB) {
    if !is_logging_enabled() {
      return;
    }
    log(loc, Debug, prefix +
        fmt_uint16("LCID: 0x%04x", p_ccb.local_cid()) + "  " +
        "st: " + l2c_csm_get_state_name(state) + "  " +
        "evt: "+ l2c_csm_get_event_name(event));
  }

  method log_csm_execution_exit(loc: string, state: ChannelState, event: tL2CEVT) {
    if !is_logging_enabled() {
      return;
    }
    log(loc, Debug, "Exit " +
        "chnl_state=" + "CST_" + l2c_csm_get_state_name(state) + " " +
        fmt_uint8("[%d]", l2c_csm_get_state_order(state)) +
        ", event="+ l2c_csm_get_event_name(event) + " " +
        fmt_uint16("[%d]", l2c_csm_get_event_order(event)));
  }

  method log_disconnect_ind(loc: string, conf_needed: bool, p_ccb: tL2C_CCB) {
    if !is_logging_enabled() {
      return;
    }
    log_disconnect_ind_gen(loc, Debug, "", conf_needed, p_ccb);
  }

  method log_disconnect_ind_incompatible(loc: string, p_ccb: tL2C_CCB) {
    if !is_logging_enabled() {
      return;
    }
    log_disconnect_ind_gen(loc, Warn, "Incompatible CFG", false, p_ccb);
  }


  method log_disconnect_ind_gen(loc: string, level: LogLevel, in_paren: string, conf_needed: bool, p_ccb: tL2C_CCB) {
    if !is_logging_enabled() {
      return;
    }
    var conf_phrase:= (if conf_needed then "" else "No ") + "Conf Needed";
    log(loc, level, "Calling Disconnect_Ind_Cb(" + in_paren + "), " + fmt_cid(p_ccb) + "  " + conf_phrase);
  }

  function fmt_cid(p_ccb: tL2C_CCB): string
    reads p_ccb`handle {
    fmt_uint16("CID: 0x%04x", p_ccb.local_cid())
  }
}
