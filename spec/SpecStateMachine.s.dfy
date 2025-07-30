/*
All Rights Reserved.

Use of this specification by anyone who is not a member of Bluetooth SIG is prohibited and is an
infringement of the intellectual property rights of Bluetooth SIG and its members.

See the LICENSE file for more details.

Copyright © 1999–2021. All copyrights in the Bluetooth Specifications themselves are owned by
Apple Inc., Ericsson AB, Intel Corporation, Lenovo (Singapore) Pte. Ltd., Microsoft Corporation,
Nokia Corporation, and Toshiba Corporation. The Bluetooth word mark and logos are owned by
Bluetooth SIG, Inc. Other third-party brands and names are the property of their respective
owners.
*/

/**
 * This module defines states, events, and actions for the state transitions in
 * the L2CAP state machine as specified in the Bluetooth Core Specification.
 */
module SpecStateMachine {
  import opened CommonTypes

  // Substates for the Config state (ref: page 1092)
  datatype ConfigSubstate = WaitConfig
                          | WaitSendConfig
                          | WaitConfigReqRsp
                          | WaitConfigRsp
                          | WaitConfigReq
                          | WaitIndFinalRsp
                          | WaitFinalRsp
                          | WaitControlInd

  // States of the L2CAP state machine (ref: page 1089)
  datatype SsmState = Closed
                    | WaitConnectRsp
                    | WaitConnect
                    | Config(substate: ConfigSubstate)
                    | Open
                    | WaitDisconnect

  // Events triggered internally at the L2CAP layer or by the controller
  datatype AbstractEvent = OpenChannelReq
                         | OpenChannelRsp
                         | ConfigureChannelReq
                         | CloseChannelReq
                         | SendDataReq
                         | ReconfigureChannelReq
                         | ControllerLogicalLinkInd
                         | Error // NOTE: augmented
                         | LeOpenChannelRsp // NOTE: augmented

  // type definition provided in chapter 4
  datatype L2cap4Event = CommandRejectRsp /* 0x01 */ /* 0x0001 and 0x0005 */
                       | ConnectionReq /* 0x02 */ /* 0x0001 */
                       | ConnectionRsp /* 0x03 */ /* 0x0001 */
                       | ConfigurationReq /* 0x04 */ /* 0x0001 */
                       | ConfigurationRsp /* 0x05 */ /* 0x0001 */
                       | DisconnectionReq /* 0x06 */ /* 0x0001 and 0x0005 */
                       | DisconnectionRsp /* 0x07 */ /* 0x0001 and 0x0005 */
                       | EchoReq /* 0x08 */ /* 0x0001 */
                       | EchoRsp /* 0x09 */ /* 0x0001 */
                       | InformationReq /* 0x0a */ /* 0x0001 */
                       | InformationRsp /* 0x0b */ /* 0x0001 */
                         // 0x0c to 0x11
                       | ConnectionParameterUpdateReq /* 0x12 */ /* 0x0005 */
                       | ConnectionParameterUpdateRsp /* 0x13 */ /* 0x0005 */
                       | LeCreditBasedConnectionReq /* 0x14 */ /* 0x0005 */
                       | LeCreditBasedConnectionRsp /* 0x15 */ /* 0x0005 */
                       | FlowControlCreditInd /* 0x16 */ /* 0x0001 and 0x0005 */
                       | CreditBasedConnectionReq /* 0x17 */ /* 0x0001 and 0x0005 */
                       | CreditBasedConnectionRsp /* 0x18 */ /* 0x0001 and 0x0005 */
                       | CreditBasedReconfigureReq /* 0x19 */ /* 0x0001 and 0x0005 */
                       | CreditBasedReconfigureRsp /* 0x1a */ /* 0x0001 and 0x0005 */

  // Config options (ref: section 6.1.4)
  datatype ConfigOption = ExtFlowSpecPlusOtherOpts
                        | NewOpts
                        | Unspecified

  // Status for events in the L2CAP state machine
  datatype SsmStatus = Success
                     | Pending
                     | Failure

  // Packet according to configured mode
  datatype DataPacket = Default

  // Events triggered by the peer device
  datatype L2cap6Event = ConnectReq
                       | ConnectRsp(status: SsmStatus)
                       | ConfigReq(option: ConfigOption)
                       | ConfigRsp(status: SsmStatus)
                       | DisconnectReq
                       | DisconnectRsp
                       | Data(data: DataPacket)
                       | CommandRejectInvalidCid
                         // NOTE: augment events for LE
                       | LeConnectReq
                       | LeConnectRsp(status: SsmStatus)

  // Events in the L2CAP state machine:
  // 1. Internal (events triggered within the same device)
  // 2. Message (events triggered by the peer device)
  datatype SsmEvent = Internal(event: AbstractEvent)
                    | Message(packet: L2cap6Event)

  // Types for config process (ref: section 6.1.4)
  datatype ConfigProcess = Standard
                         | Lockstep

  // Bluetooth operating modes: Classic and Low Energy
  datatype Configuration = BasicRate(process: ConfigProcess) // BR/EDR
                         | LowEnergy

  // Conditions for the L2CAP state machine, including the config process and status
  datatype SsmCondition = SsmCondition(process: ConfigProcess, status: SsmStatus)

  // Datatype combining event and condition for verification proof
  type SsmEventCondition = (SsmEvent, SsmCondition)

  // Actions in the L2CAP state machine across state event tables
  datatype SsmAction = Send(event: L2cap6Event)
                     | Ignore
                     | ProcessPdu
                     | CompleteSdu
                       /**/
                     | Seq(action1: SsmAction, action2: SsmAction)

  // Output of a state transition: an optional action and the next state
  datatype SsmActionStatePair = SsmPair(action: Option<SsmAction>, state: SsmState)

  // The state machine is represented as a function
  // that takes the current state, event, and condition as input
  // and returns an action and the next state as output
  ghost function ExecuteSsmModel(state: SsmState, event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match state {
      case Closed => table_closed(event, condition)
      case WaitConnectRsp => table_wait_connect_rsp(event, condition)
      case WaitConnect => table_wait_connect(event, condition)
      case Config(config) => subtable_config(config, event, condition)
      case Open => table_open(event, condition)
      case WaitDisconnect => table_wait_disconnect(event, condition)
    }
  }

  // Ref: table 6.1
  ghost function table_closed(event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match event {
      case Internal(OpenChannelReq) =>
        SsmPair(Some(Send(ConnectReq)), WaitConnectRsp)
      case Internal(Error) =>
        SsmPair(None, Closed)
      case Message(event) =>
        match event {
          case ConnectReq =>
            match condition {
              case SsmCondition(_, Success) =>
                SsmPair(Some(Send(ConnectRsp(Success))), Config(WaitConfig))
              case SsmCondition(_, Pending) =>
                SsmPair(Some(Send(ConnectRsp(Pending))), WaitConnect)
              case SsmCondition(_, Failure) =>
                SsmPair(Some(Send(ConnectRsp(Failure))), Closed)
            }
          case LeConnectReq =>
            match condition {
              case SsmCondition(_, Success) =>
                SsmPair(Some(Send(LeConnectRsp(Success))), Open)
              case SsmCondition(_, Pending) =>
                SsmPair(None, WaitConnect)
              case SsmCondition(_, Failure) =>
                SsmPair(Some(Send(LeConnectRsp(Failure))), Closed)
            }
          case ConnectRsp(_) =>
            SsmPair(Some(Ignore), Closed)
          case ConfigReq(_) =>
            SsmPair(Some(Send(CommandRejectInvalidCid)), Closed)
          case ConfigRsp(_) =>
            SsmPair(Some(Ignore), Closed)
          case DisconnectReq =>
            SsmPair(Some(Send(DisconnectRsp)), Closed)
          case DisconnectRsp =>
            SsmPair(Some(Ignore), Closed)
          case Data(_) =>
            SsmPair(Some(Ignore), Closed)
          case _ =>
            SsmPair(Some(Ignore), Closed)
        }
      case _ =>
        SsmPair(Some(Ignore), Closed)
    }
  }

  // Ref: table 6.2
  ghost function table_wait_connect_rsp(event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match event {
      case Internal(Error) =>
        SsmPair(None, Closed)
      case Internal(CloseChannelReq) =>
        SsmPair(Some(Send(DisconnectReq)), WaitDisconnect)
      case Message(event) =>
        match event {
          case ConnectRsp(Success) =>
            SsmPair(Some(Send(ConfigReq(Unspecified))), Config(WaitConfig))
          case LeConnectRsp(Success) =>
            SsmPair(None, Open)
          case ConnectRsp(Pending) | LeConnectRsp(Pending) =>
            SsmPair(None, WaitConnectRsp)
          case ConnectRsp(Failure) | LeConnectRsp(Failure) =>
            SsmPair(None, Closed)
          case ConfigReq(_) =>
            SsmPair(Some(Send(CommandRejectInvalidCid)), WaitConnectRsp)
          case ConfigRsp(_) =>
            SsmPair(Some(Ignore), WaitConnectRsp)
          case DisconnectRsp =>
            SsmPair(Some(Ignore), WaitConnectRsp)
          case Data(_) =>
            SsmPair(Some(Ignore), WaitConnectRsp)
          case _ =>
            SsmPair(Some(Ignore), WaitConnectRsp)
        }
      case _ =>
        SsmPair(Some(Ignore), WaitConnectRsp)
    }
  }

  // Ref: table 6.3
  ghost function table_wait_connect(event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match event {
      case Internal(OpenChannelRsp) =>
        match condition {
          case SsmCondition(_, Success) =>
            SsmPair(Some(Send(ConnectRsp(Success))), Config(WaitConfig))
          case SsmCondition(_, Failure) =>
            SsmPair(Some(Send(ConnectRsp(Failure))), Closed)
          case _ =>
            SsmPair(Some(Ignore), WaitConnect)
        }
      case Internal(LeOpenChannelRsp) =>
        match condition {
          case SsmCondition(_, Success) =>
            SsmPair(Some(Send(LeConnectRsp(Success))), Open)
          case SsmCondition(_, Failure) =>
            SsmPair(Some(Send(LeConnectRsp(Failure))), Closed)
          case _ =>
            SsmPair(Some(Ignore), WaitConnect)
        }
      case Internal(Error) =>
        SsmPair(None, Closed)
      case Internal(CloseChannelReq) =>
        SsmPair(Some(Send(DisconnectReq)), WaitDisconnect)
      case Message(event) =>
        match event {
          case ConnectRsp(_) =>
            SsmPair(Some(Ignore), WaitConnect)
          case ConfigRsp(_) =>
            SsmPair(Some(Ignore), WaitConnect)
          case DisconnectRsp =>
            SsmPair(Some(Ignore), WaitConnect)
          case Data(_) =>
            SsmPair(Some(Ignore), WaitConnect)
          case _ =>
            SsmPair(Some(Ignore), WaitConnect)
        }
      case _ =>
        SsmPair(Some(Ignore), WaitConnect)
    }
  }

  // Ref: table 6.4, 6.5, & 6.6
  ghost function subtable_config(substate: ConfigSubstate, event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match(substate, event, condition) {
      // table 6.4(part 1)
      case (WaitConfig, Internal(ConfigureChannelReq), SsmCondition(Standard, _)) =>
        SsmPair(Some(Send(ConfigReq(Unspecified))), Config(WaitConfigReqRsp))
      case (WaitConfig, Internal(ConfigureChannelReq), SsmCondition(Lockstep, _)) =>
        SsmPair(Some(Send(ConfigReq(ExtFlowSpecPlusOtherOpts))), Config(WaitConfigReqRsp))
      case (WaitConfig, Message(ConfigReq(_)), SsmCondition(Standard, Pending)) =>
        SsmPair(Some(Send(ConfigRsp(Success))), Config(WaitSendConfig))
      case (WaitConfig, Message(ConfigReq(_)), SsmCondition(Lockstep, Pending)) =>
        SsmPair(Some(Send(ConfigRsp(Pending))), Config(WaitSendConfig))
      case (WaitConfigReqRsp, Message(ConfigReq(_)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Send(ConfigRsp(Success))), Config(WaitConfigRsp))
      case (WaitConfigReqRsp, Message(ConfigRsp(Success)), SsmCondition(_, Pending)) =>
        SsmPair(None, Config(WaitConfigReq))
      case (WaitConfigReq, Message(ConfigReq(_)), SsmCondition(Standard, Success)) =>
        SsmPair(Some(Send(ConfigRsp(Success))), Open)
      case (WaitConfigReq, Message(ConfigReq(_)), SsmCondition(Lockstep, Success)) =>
        SsmPair(Some(Send(ConfigRsp(Pending))), Config(WaitIndFinalRsp))
      case (WaitSendConfig, Internal(ConfigureChannelReq), _) =>
        SsmPair(Some(Send(ConfigReq(Unspecified))), Config(WaitConfigRsp))

      // table 6.4(part 2)
      case (WaitConfigRsp, Message(ConfigRsp(Success)), SsmCondition(Standard, Success)) =>
        SsmPair(None, Open)
      case (WaitConfigRsp, Message(ConfigRsp(Success)), SsmCondition(Lockstep, Pending)) =>
        SsmPair(None, Config(WaitIndFinalRsp))
      case (WaitIndFinalRsp, Internal(ControllerLogicalLinkInd), SsmCondition(_ /* FIXME: potential ambiguity: only standard or also lockstep? */, Failure)) =>
        SsmPair(Some(Send(ConfigRsp(Failure))), Config(WaitConfig))
      case (WaitIndFinalRsp, Internal(ControllerLogicalLinkInd), SsmCondition(_ /* FIXME: potential ambiguity: only standard or also lockstep? */, Pending)) =>
        SsmPair(Some(Send(ConfigRsp(Success))), Config(WaitFinalRsp))
      case (WaitIndFinalRsp, Message(ConfigRsp(Failure)), SsmCondition(_, Pending)) =>
        SsmPair(None, Config(WaitConfig))
      case (WaitIndFinalRsp, Message(ConfigRsp(Success)), SsmCondition(_, Pending)) =>
        SsmPair(None, Config(WaitControlInd))
      case (WaitFinalRsp, Message(ConfigRsp(Failure)), SsmCondition(_, Pending)) =>
        SsmPair(None, Config(WaitConfig))
      case (WaitFinalRsp, Message(ConfigRsp(Success)), SsmCondition(_, Success)) =>
        SsmPair(None, Open)
      case (WaitControlInd, Internal(ControllerLogicalLinkInd), SsmCondition(_ /* FIXME: potential ambiguity: only standard or also lockstep? */, Failure)) =>
        SsmPair(Some(Send(ConfigRsp(Failure))), Config(WaitConfig))
      case (WaitControlInd, Internal(ControllerLogicalLinkInd), SsmCondition(_ /* FIXME: potential ambiguity: only standard or also lockstep? */, Success)) =>
        SsmPair(Some(Send(ConfigRsp(Success))), Open)

      // table 6.5
      case (WaitConfig, Message(ConfigReq(_)), SsmCondition(_, Failure /* FIXME: exhaustivity? */)) =>
        SsmPair(Some(Send(ConfigRsp(Failure))), Config(WaitConfig))
      case (WaitConfig, Message(ConfigRsp(_)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Ignore), Config(WaitConfig))
      case (WaitSendConfig, Message(ConfigRsp(_)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Ignore), Config(WaitSendConfig))
      case (WaitConfigReqRsp, Message(ConfigReq(_)), SsmCondition(_, Failure)) =>
        SsmPair(Some(Send(ConfigRsp(Failure))), Config(WaitConfigReqRsp))
      case (WaitConfigReqRsp, Message(ConfigRsp(Failure)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Send(ConfigReq(NewOpts))), Config(WaitConfigReqRsp))
      case (WaitConfigReq, Message(ConfigReq(_)), SsmCondition(_, Failure)) =>
        SsmPair(Some(Send(ConfigRsp(Failure))), Config(WaitConfigReq))
      case (WaitConfigReq, Message(ConfigRsp(_)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Ignore), Config(WaitConfigReq))
      case (WaitConfigRsp, Message(ConfigRsp(Failure)), SsmCondition(_, Pending)) =>
        SsmPair(Some(Send(ConfigReq(NewOpts))), Config(WaitConfigRsp))

      // table 6.6
      case (_, Internal(CloseChannelReq), _ /* NOTE: ``Any internal reason to stop'' */) =>
        SsmPair(Some(Send(DisconnectReq)), WaitDisconnect)
      case (_, Message(DisconnectReq), _) =>
        SsmPair(Some(Send(DisconnectRsp)), Closed)
      case (_, Message(DisconnectRsp), _) =>
        SsmPair(Some(Ignore), Config(substate))
      case (_, Message(Data(_)), _) =>
        SsmPair(Some(ProcessPdu), Config(substate))
      case (_, Internal(Error), _) =>
        SsmPair(None, Closed)

      //
      case _ =>
        SsmPair(Some(Ignore), Config(substate))
    }
  }

  // Ref: table 6.7
  ghost function table_open(event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match event {
      case Internal(SendDataReq) =>
        SsmPair(Some(Send(Data(Default))), Open)
      case Internal(ReconfigureChannelReq) =>
        SsmPair(Some(Seq(CompleteSdu, Send(ConfigReq(Unspecified)))), Config(WaitConfigReqRsp))
      case Internal(CloseChannelReq) =>
        SsmPair(Some(Send(DisconnectReq)), WaitDisconnect)
      case Internal(Error) =>
        SsmPair(None, Closed)
      case Message(event) =>
        match event {
          case ConnectRsp(_) =>
            SsmPair(Some(Ignore), Open)
          case ConfigReq(_) =>
            match condition {
              case SsmCondition(_, Success) =>
                SsmPair(Some(Seq(CompleteSdu, Send(ConfigRsp(Success) /* NOTE: ambiguous "ok" treated as success */))), Config(WaitSendConfig))
              case SsmCondition(_, Failure) =>
                SsmPair(Some(Seq(CompleteSdu, Send(ConfigRsp(Failure)))), Open)
              case _ =>
                SsmPair(Some(Ignore), Open)
            }
          case DisconnectReq =>
            SsmPair(Some(Send(DisconnectRsp)), Closed)
          case DisconnectRsp =>
            SsmPair(Some(Ignore), Open)
          case Data(_) =>
            SsmPair(Some(ProcessPdu), Open)
          case _ =>
            SsmPair(Some(Ignore), Open)
        }
      case _ =>
        SsmPair(Some(Ignore), Open)
    }
  }

  // Ref: table 6.8
  ghost function table_wait_disconnect(event: SsmEvent, condition: SsmCondition): SsmActionStatePair {
    match event {
      case Internal(Error) =>
        SsmPair(None, Closed)
      case Message(event) =>
        match event {
          // table 6.8(part 1)
          case ConnectRsp(_) =>
            SsmPair(Some(Ignore), WaitDisconnect)
          case ConfigReq(_) =>
            SsmPair(Some(Send(CommandRejectInvalidCid)), WaitDisconnect)
          case ConfigRsp(_) =>
            SsmPair(Some(Ignore), WaitDisconnect)
          case DisconnectReq =>
            SsmPair(Some(Send(DisconnectRsp)), Closed)
          // table 6.8(part 2)
          case DisconnectRsp =>
            SsmPair(None, Closed)
          case Data(_) =>
            SsmPair(Some(Ignore), WaitDisconnect)
          case _ =>
            SsmPair(Some(Ignore), WaitDisconnect)
        }
      case _ =>
        SsmPair(Some(Ignore), WaitDisconnect)
    }
  }
}
