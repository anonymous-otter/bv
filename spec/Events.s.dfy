
/**
 * This module defines predicates to check if an event is a valid or error event
 * for the current state of the state machine.
 */
module Events {
  import opened OpsStateMachine

  // Check if an event is an error event for the current state
  ghost predicate IsErrorEvent(s: OsmState, e: OsmEvent) {
    match e {
      case Local(SecurityCheckComplete(Failure)) =>
        s == Created || s == InitiatorWaitSecurityCheck || s == AcceptorWaitSecurityCheck
      case Local(InternalFailure) =>
        s == WaitPeerConnectResponse || s == WaitLocalConnectResponse || s == Config || s == Open
      case Local(LinkDisconnectInd) | Local(Timeout) => true
      case _ => false
    }
  }

  // Check if an event is a valid event for the current state
  ghost predicate IsModeledEvent(s: OsmState, e: OsmEvent) {
    match s {
      case Created =>
        match e {
          case Local(OpenChannelReq)
            | Local(SecurityCheckComplete(Success(_, _)))
            | Local(SecurityCheckComplete(Pending))
            | Local(SecurityCheckComplete(Failure))
            | Local(SecurityCheckComplete(Resend))
            | Packet(ConnectReq)
            | Packet(ConfigReq(_))
            | Local(DisconnectReq)
            | Packet(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            => true
          case _ => false
        }
      case InitiatorWaitSecurityCheck =>
        match e {
          case Local(SecurityCheckComplete(Success(_, _)))
            | Local(SecurityCheckComplete(Failure))
            | Local(SecurityCheckComplete(Resend))
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            => true
          case _ => false
        }
      case AcceptorWaitSecurityCheck =>
        match e {
          case Local(SecurityCheckComplete(Success(_, _)))
            | Local(SecurityCheckComplete(Failure))
            | Local(SecurityCheckComplete(Pending))
            | Local(SecurityCheckComplete(Resend))
            | Packet(DisconnectReq)
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            => true
          case _ => false
        }
      case WaitPeerConnectResponse =>
        match e {
          case Packet(ConnectRsp(_, _))
            | Packet(PeerInfoRsp(_))
            | Packet(ConfigReq(_))
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            | Local(InternalFailure)
            => true
          case _ => false
        }
      case WaitLocalConnectResponse =>
        match e {
          case Local(OpenChannelRsp(_, _))
            | Packet(PeerInfoRsp(_))
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            | Local(InternalFailure)
            => true
          case _ => false
        }
      case Config =>
        match e {
          case Local(ConfigRsp(Success))
            | Local(ConfigRsp(Reconfig))
            | Local(ConfigRsp(Failure(_)))
            | Local(ConfigReq(Success))
            | Local(ConfigReq(Reconfig))
            | Local(WriteData)
            | Packet(ConfigRsp(_))
            | Packet(ConfigReq(_))
            | Packet(DisconnectReq)
            | Packet(Data)
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            | Local(InternalFailure)
            => true
          case _ => false
        }
      case Open =>
        match e {
          case Packet(Data)
            | Packet(Credit(true))
            | Local(ConfigReq(Success))
            | Local(ConfigReq(Reconfig))
            | Local(ConfigRsp(Success))
            | Local(ConfigRsp(Reconfig))
            | Local(ConfigRsp(Failure(_)))
            | Local(WriteData)
            | Packet(DisconnectReq)
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            | Local(InternalFailure)
            => true
          case _ => false
        }
      case WaitPeerDisconnectResponse =>
        match e {
          case Packet(DisconnectRsp)
            | Packet(DisconnectReq)
            | Packet(ConnectReq)
            | Packet(ConfigReq(_))
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            => true
          case _ => false
        }
      case WaitLocalDisconnectResponse =>
        match e {
          case Local(DisconnectRsp)
            | Local(DisconnectReq)
            | Local(LinkDisconnectInd)
            | Local(Timeout)
            => true
          case _ => false
        }
      case _ => false
    }
  }
}
