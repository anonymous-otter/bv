module Impl.Constants
{

  import opened Types

  const IB_CFG_DONE: bv8 := 0x01
  const OB_CFG_DONE: bv8 := 0x02
  const RECONFIG_FLAG: bv8 := 0x04

  const CCB_FLAG_NO_RETRY: bv8 := 0x01
  // const CCB_FLAG_SENT_PENDING: bv8 := 0x02

  const L2CAP_PEER_CFG_UNACCEPTABLE: uint8_t := 0
  const L2CAP_PEER_CFG_OK: uint8_t := 1
  const L2CAP_PEER_CFG_DISCONNECT: uint8_t := 2

  /*
   * Timeout values (in milliseconds).
   */
  const L2CAP_LINK_ROLE_SWITCH_TIMEOUT_MS : uint64_t := (10 * 1000)  /* 10 seconds */
  const L2CAP_LINK_CONNECT_TIMEOUT_MS : uint64_t := (60 * 1000)      /* 30 seconds */
  const L2CAP_LINK_CONNECT_EXT_TIMEOUT_MS : uint64_t := (120 * 1000) /* 120 seconds */
  const L2CAP_LINK_FLOW_CONTROL_TIMEOUT_MS : uint64_t := (2 * 1000)  /* 2 seconds */
  const L2CAP_LINK_DISCONNECT_TIMEOUT_MS : uint64_t := (30 * 1000)   /* 30 seconds */
  const L2CAP_CHNL_CONNECT_TIMEOUT_MS : uint64_t := (60 * 1000)      /* 60 seconds */
  const L2CAP_CHNL_CONNECT_EXT_TIMEOUT_MS : uint64_t := (120 * 1000) /* 120 seconds */
  const L2CAP_CHNL_CFG_TIMEOUT_MS : uint64_t := (30 * 1000)          /* 30 seconds */
  const L2CAP_CHNL_DISCONNECT_TIMEOUT_MS : uint64_t := (10 * 1000)   /* 10 seconds */
  const L2CAP_DELAY_CHECK_SM4_TIMEOUT_MS : uint64_t := (2 * 1000)    /* 2 seconds */
  const L2CAP_WAIT_INFO_RSP_TIMEOUT_MS : uint64_t := (3 * 1000)      /* 3 seconds */
  const L2CAP_BLE_LINK_CONNECT_TIMEOUT_MS : uint64_t := (30 * 1000)  /* 30 seconds */
  const L2CAP_FCR_ACK_TIMEOUT_MS : uint64_t := 200                   /* 200 milliseconds */


  const L2CAP_FCR_BASIC_MODE : uint8_t := 0x00
  const L2CAP_FCR_ERTM_MODE : uint8_t := 0x03
  const L2CAP_FCR_LE_COC_MODE : uint8_t := 0x05



  /******************************************************************************
   *
   * L2CAP
   *
   *****************************************************************************/

  /* The maximum number of simultaneous links that L2CAP can support. */
  const MAX_L2CAP_LINKS: uint16_t := 13

  /* The maximum number of simultaneous channels that L2CAP can support. */
  const MAX_L2CAP_CHANNELS: uint16_t := 32

  /* The maximum number of simultaneous applications that can register with L2CAP.
   */
  const MAX_L2CAP_CLIENTS: uint16_t := 15

  /* The L2CAP MTU; must be in accord with the HCI ACL buffer size. */
  const L2CAP_MTU_SIZE: uint16_t := 1691

  /* Used for features using fixed channels; set to zero if no fixed channels
   * supported (BLE, etc.) */
  /* Excluding L2CAP signaling channel and UCD */
  const L2CAP_NUM_FIXED_CHNLS: uint16_t := 32

  /* First fixed channel supported */
  const L2CAP_FIRST_FIXED_CHNL: uint16_t := 4

  const L2CAP_LAST_FIXED_CHNL: uint16_t := (L2CAP_FIRST_FIXED_CHNL + L2CAP_NUM_FIXED_CHNLS - 1)



  // const L2cap_Trace_Error := "L2cap_Trace_Error"
  // const L2cap_Trace_Warning := "L2cap_Trace_Warning"
  // const L2cap_Trace_Api := "L2cap_Trace_Api"
  // const L2cap_Trace_Event := "L2cap_Trace_Event"
  // const L2cap_Trace_Debug := "L2cap_Trace_Debug"

  // const Log_Tag_Verbose := "Log_Tag_Verbose"
  // const Log_Tag_Debug := "Log_Tag_Debug"
  // const Log_Tag_Info := "Log_Tag_Info"
  // const Log_Tag_Warn := "Log_Tag_Warn"
  // const Log_Tag_Error := "Log_Tag_Error"
  // const Log_Tag_Fatal := "Log_Tag_Fatal"


  // const BTM_SUCCESS : tBTM_STATUS := 0             /* 0  Command succeeded                 */
  const BTM_CMD_STARTED : tBTM_STATUS := 1         /* 1  Command started OK.               */
  // const BTM_BUSY : tBTM_STATUS := 2                /* 2  Device busy with another command  */
  // const BTM_NO_RESOURCES : tBTM_STATUS := 3        /* 3  No resources to issue command     */
  // const BTM_MODE_UNSUPPORTED : tBTM_STATUS := 4    /* 4  Request for 1 or more unsupported modes */
  // const BTM_ILLEGAL_VALUE : tBTM_STATUS := 5       /* 5  Illegal parameter value           */
  // const BTM_WRONG_MODE : tBTM_STATUS := 6          /* 6  Device in wrong mode for request  */
  // const BTM_UNKNOWN_ADDR : tBTM_STATUS := 7        /* 7  Unknown remote BD address         */
  // const BTM_DEVICE_TIMEOUT : tBTM_STATUS := 8      /* 8  Device timeout                    */
  // const BTM_BAD_VALUE_RET : tBTM_STATUS := 9       /* 9  A bad value was received from HCI */
  // const BTM_ERR_PROCESSING : tBTM_STATUS := 10      /* 10 Generic error                     */
  // const BTM_NOT_AUTHORIZED : tBTM_STATUS := 11      /* 11 Authorization failed              */
  // const BTM_DEV_RESET : tBTM_STATUS := 12           /* 12 Device has been reset             */
  // const BTM_CMD_STORED : tBTM_STATUS := 13          /* 13 request is stored in control block */
  // const BTM_ILLEGAL_ACTION : tBTM_STATUS := 14      /* 14 state machine gets illegal command */
  const BTM_DELAY_CHECK : tBTM_STATUS := 15         /* 15 delay the check on encryption */
  // const BTM_SCO_BAD_LENGTH : tBTM_STATUS := 16      /* 16 Bad SCO over HCI data length */
  // const BTM_SUCCESS_NO_SECURITY : tBTM_STATUS := 17 /* 17 security passed, no security set  */
  // const BTM_FAILED_ON_SECURITY : tBTM_STATUS := 18  /* 18 security failed                   */
  // const BTM_REPEATED_ATTEMPTS : tBTM_STATUS := 19   /* 19 repeated attempts for LE security requests */
  // const BTM_MODE4_LEVEL4_NOT_SUPPORTED : tBTM_STATUS := 20 /* 20 Secure Connections Only Mode can't be
  //                                                         supported */
  // const BTM_DEV_RESTRICT_LISTED : tBTM_STATUS := 21        /* 21 The device is restrict listed */
  // const BTM_MAX_STATUS_VALUE : tBTM_STATUS := BTM_DEV_RESTRICT_LISTED
  // const BTM_UNDEFINED : tBTM_STATUS := 0xFF

  type tHCI_REASON = uint8_t

  const HCI_ERR_CONNECTION_EXISTS: tHCI_REASON := 0x0B
  // TODO: Add more modes and error codes

  type tHCI_ERROR_CODE = uint8_t

  const HCI_ERR_AUTH_FAILURE: tHCI_ERROR_CODE := 0x05
  const HCI_ERR_PEER_USER: tHCI_ERROR_CODE := 0x13
  const HCI_ERR_CONN_CAUSE_LOCAL_HOST: tHCI_ERROR_CODE := 0x16

  const L2CAP_CFG_OK: uint16_t := 0
  const L2CAP_CFG_UNACCEPTABLE_PARAMS: uint16_t := 1
  const L2CAP_CFG_FAILED_NO_REASON: uint16_t := 2
  const L2CAP_CFG_UNKNOWN_OPTIONS: uint16_t := 3
  const L2CAP_CFG_PENDING: uint16_t := 4

  /* Define the L2CAP connection result codes
   */
  type tL2CAP_CONN = uint16_t

  const L2CAP_CONN_OK : tL2CAP_CONN := 0
  const L2CAP_CONN_PENDING : tL2CAP_CONN := 1
  const L2CAP_CONN_NO_PSM : tL2CAP_CONN := 2
  const L2CAP_CONN_SECURITY_BLOCK : tL2CAP_CONN := 3
  const L2CAP_CONN_NO_RESOURCES : tL2CAP_CONN := 4
  const L2CAP_CONN_OTHER_ERROR : tL2CAP_CONN := 5
  const L2CAP_CONN_TIMEOUT : uint16_t := 0xEEEE
  /* Add a couple of our own for internal use */
  const L2CAP_CONN_NO_LINK : tL2CAP_CONN := 255
  const L2CAP_CONN_CANCEL : tL2CAP_CONN := 256 /* L2CAP connection cancelled */

  /* Define the LE L2CAP Connection Response Result codes
   */


  const L2CAP_LE_RESULT_CONN_OK : tL2CAP_LE_RESULT_CODE := 0
  const L2CAP_LE_RESULT_NO_PSM : tL2CAP_LE_RESULT_CODE := 2
  const L2CAP_LE_RESULT_NO_RESOURCES: tL2CAP_LE_RESULT_CODE := 4
  const L2CAP_LE_RESULT_INSUFFICIENT_AUTHENTICATION : tL2CAP_LE_RESULT_CODE := 5
  const L2CAP_LE_RESULT_INSUFFICIENT_AUTHORIZATION : tL2CAP_LE_RESULT_CODE := 6
  const L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP_KEY_SIZE : tL2CAP_LE_RESULT_CODE := 7
  const L2CAP_LE_RESULT_INSUFFICIENT_ENCRYP : tL2CAP_LE_RESULT_CODE := 8
  /* We don't like peer device response */
  const L2CAP_LE_RESULT_INVALID_SOURCE_CID : tL2CAP_LE_RESULT_CODE := 9
  const L2CAP_LE_RESULT_SOURCE_CID_ALREADY_ALLOCATED : tL2CAP_LE_RESULT_CODE := 0x0A
  const L2CAP_LE_RESULT_UNACCEPTABLE_PARAMETERS : tL2CAP_LE_RESULT_CODE := 0x0B
  const L2CAP_LE_RESULT_INVALID_PARAMETERS : tL2CAP_LE_RESULT_CODE := 0x0C

  /* L2CAP Predefined CIDs
   */
  const L2CAP_ATT_CID: uint16_t := 0x0004
  const L2CAP_SMP_CID: uint16_t := 0x0006
  const L2CAP_BASE_APPL_CID: uint16_t := 0x0040

  const L2CAP_EXTFEA_ENH_RETRANS: bv32 := 0x00000008

  const L2CAP_CFG_FLAGS_MASK_CONT: bv16 := 0x0001
}