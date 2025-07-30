// Operational State Machine
module OpsStateMachine {
  import opened CommonTypes

  // Available operating modes in Bluetooth
  datatype ConnectionMode = Ble | Classic | CreditBased

  // The result of the security check
  datatype CheckResult =
    | Success(should_wait_info: bool, mode: ConnectionMode)
    | Pending
    | Failure
    | Resend

  // The result of the connection response
  datatype ConnectRspResult =
    | Success
    | Pending
    | Refused

  // The result of the configuration response
  datatype ConfigResult =
    | Success
    | Failure(should_disconnect: bool)
    | Reconfig
    | Pending

  // Events that are triggered locally within the same device
  datatype LocalEvent =
    | OpenChannelReq
    | OpenChannelRsp(response: ConnectRspResult, mode: ConnectionMode)
    | SecurityCheckComplete(result: CheckResult)
    | ConfigReq(cfg_result: ConfigResult)
    | ConfigRsp(cfg_result: ConfigResult)
    | DisconnectReq
    | DisconnectRsp
    | WriteData
    | SendCredit
    | LinkDisconnectInd
    | Timeout
    | InternalFailure // for incompatible channels, mismatched connection modes, etc.
    | Revive

  // Events that are triggered by the peer device
  datatype PacketEvent =
    | ConnectReq
    | ConnectRsp(result: ConnectRspResult, mode: ConnectionMode)
    | ConfigReq(cfg_done: bool)
    | ConfigRsp(cfg_result: ConfigResult)
    | DisconnectReq
    | DisconnectRsp
    | Data
    | PeerInfoRsp(mode: ConnectionMode)
    | Credit(max_credit_exceeded: bool)

  // Events in the state machine:
  // 1. A sequence of events
  // 2. A local event triggered by the local device
  // 3. A packet event triggered by the peer device
  // 4. An unmodeled event
  datatype OsmEvent =
    | Seq(events: seq<OsmEvent>)
    | Local(local_event: LocalEvent)
    | Packet(packet_event: PacketEvent)
    | Unmodeled

  // States of the state machine
  datatype OsmState =
    | Created
    | Destroyed
    | InitiatorWaitSecurityCheck
    | AcceptorWaitSecurityCheck
    | WaitPeerConnectResponse
    | WaitLocalConnectResponse
    | Config
    | Open
    | WaitPeerDisconnectResponse
    | WaitLocalDisconnectResponse

  // Actions that can be taken in the state machine
  datatype OsmAction =
    | Seq(actions: seq<OsmAction>)
    | SendConnectReq
    | SendConnectRsp(result: ConnectRspResult)
    | SendConfigReq
    | SendConfigRsp
    | SendCommandReject
    | SendDisconnectReq
    | SendDisconnectRsp
    | CheckSecurityRequirements
    | AbortSecAccessReq
    | ProcessPDU
    | SendData

  // Output of a state transition: an optional action and the next state
  datatype OsmActionStatePair = OsmPair(action: Option<OsmAction>, state: OsmState)

  // The state machine is represented as a function
  // that takes the current state, event, and condition as input
  // and returns an action and the next state as output
  ghost function ExecuteOsmModel(state: OsmState, event: OsmEvent): OsmActionStatePair {
    match state {
      case Created => CreatedModel(event)
      case InitiatorWaitSecurityCheck => InitiatorWaitSecurityCheckModel(event)
      case WaitPeerConnectResponse => WaitPeerConnectResponseModel(event)
      case AcceptorWaitSecurityCheck => AcceptorWaitSecurityCheckModel(event)
      case WaitLocalConnectResponse => WaitLocalConnectResponseModel(event)
      case Config => ConfigModel(event)
      case Open => OpenModel(event)
      case WaitPeerDisconnectResponse => WaitPeerDisconnectResponseModel(event)
      case WaitLocalDisconnectResponse => WaitLocalDisconnectResponseModel(event)
      case Destroyed => OsmPair(None, state)
    }
  }

  // Execute the state machine with a sequence of events
  ghost function ExecuteOsmModelSeq(current_state: OsmState, events: seq<OsmEvent>): OsmActionStatePair
    requires |events| > 0
    decreases |events|
  {
    if |events| == 1 then
      ExecuteOsmModel(current_state, events[0])
    else
      var next := ExecuteOsmModel(current_state, events[0]);
      ExecuteOsmModelSeq(next.state, events[1..])
  }

  // Current state: Created
  ghost function CreatedModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(OpenChannelReq) =>
        OsmPair(Some(CheckSecurityRequirements), InitiatorWaitSecurityCheck)
      case Local(SecurityCheckComplete(Success(false, _))) =>
        OsmPair(Some(SendConnectReq), WaitPeerConnectResponse)
      case Local(SecurityCheckComplete(Success(true, _))) =>
        OsmPair(None, WaitPeerConnectResponse)
      case Local(SecurityCheckComplete(Pending)) =>
        OsmPair(None, InitiatorWaitSecurityCheck)
      case Local(SecurityCheckComplete(Failure)) =>
        OsmPair(None, Destroyed)
      case Local(SecurityCheckComplete(Resend)) =>
        OsmPair(Some(CheckSecurityRequirements), Created)
      case Packet(ConnectReq) =>
        OsmPair(Some(CheckSecurityRequirements), AcceptorWaitSecurityCheck)
      case Packet(ConfigReq(_)) =>
        OsmPair(Some(SendCommandReject), Created)
      case Packet(ConnectRsp(_, _)) | Packet(ConfigRsp(_)) | Packet(DisconnectRsp) | Packet(Data) | Local(WriteData) =>
        OsmPair(None, Created)
      case Local(DisconnectReq) =>
        OsmPair(None, Destroyed)
      case Packet(DisconnectReq) =>
        OsmPair(Some(SendDisconnectRsp), Destroyed)
      case Local(Timeout) | Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, Created)
    }
  }

  // Current state: Destroyed
  ghost function DestroyedModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(Revive) =>
        OsmPair(None, Created)
      case _ =>
        OsmPair(None, Destroyed)
    }
  }

  // Current state: InitiatorWaitSecurityCheck
  ghost function InitiatorWaitSecurityCheckModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(SecurityCheckComplete(Resend)) =>
        OsmPair(Some(CheckSecurityRequirements), InitiatorWaitSecurityCheck)
      case Local(SecurityCheckComplete(Success(_, Ble)))
        | Local(SecurityCheckComplete(Success(_, CreditBased)))
        | Local(SecurityCheckComplete(Success(false, Classic))) =>
        OsmPair(Some(SendConnectReq), WaitPeerConnectResponse)
      case Local(SecurityCheckComplete(Success(true, Classic))) =>
        OsmPair(None, WaitPeerConnectResponse)
      case Local(SecurityCheckComplete(Failure)) =>
        OsmPair(None, Destroyed)
      case Local(DisconnectReq) =>
        OsmPair(Some(AbortSecAccessReq), Destroyed)
      case Packet(ConnectRsp(_, _)) | Packet(ConfigRsp(_)) | Packet(DisconnectRsp) | Packet(Data) | Local(WriteData) =>
        OsmPair(None, InitiatorWaitSecurityCheck)
      case Local(LinkDisconnectInd) | Local(Timeout) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, InitiatorWaitSecurityCheck)
    }
  }

  // Current state: WaitPeerConnectResponse
  ghost function WaitPeerConnectResponseModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Packet(ConnectRsp(Success, CreditBased)) | Packet(ConnectRsp(Success, Ble)) =>
        OsmPair(None, Open)
      case Packet(ConnectRsp(Success, Classic)) =>
        OsmPair(None, OsmState.Config)
      case Packet(ConnectRsp(Pending, _)) =>
        OsmPair(None, WaitPeerConnectResponse)
      case Packet(ConnectRsp(Refused, _)) =>
        OsmPair(None, Destroyed)
      case Local(DisconnectReq) =>
        OsmPair(Some(SendDisconnectReq), WaitPeerDisconnectResponse)
      case Packet(PeerInfoRsp(_)) =>
        OsmPair(Some(SendConnectReq), WaitPeerConnectResponse)
      case Packet(ConfigReq(_)) =>
        OsmPair(Some(SendCommandReject), WaitPeerConnectResponse)
      case Packet(ConfigRsp(_)) | Packet(DisconnectRsp) | Packet(Data) | Local(WriteData) =>
        OsmPair(None, WaitPeerConnectResponse)
      case Local(Timeout) | Local(LinkDisconnectInd) | Local(InternalFailure) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, WaitPeerConnectResponse)
    }
  }

  // Current state: AcceptorWaitSecurityCheck
  ghost function AcceptorWaitSecurityCheckModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(LinkDisconnectInd) =>
        OsmPair(Some(AbortSecAccessReq), Destroyed)
      case Local(SecurityCheckComplete(Success(false, Classic))) =>
        // OsmPair(Some(SendConnectRsp(ConnectRspResult.Success)), Config)
        OsmPair(None, WaitLocalConnectResponse)
      case Local(SecurityCheckComplete(Success(false, Ble))) =>
        // OsmPair(Some(SendConnectRsp(ConnectRspResult.Success)), Open)
        OsmPair(None, WaitLocalConnectResponse)
      case Local(SecurityCheckComplete(Success(false, CreditBased))) =>
        OsmPair(None, WaitLocalConnectResponse)
      case Local(SecurityCheckComplete(Pending)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Pending)), AcceptorWaitSecurityCheck)
      case Local(SecurityCheckComplete(Success(true, _))) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Pending)), WaitLocalConnectResponse)
      case Local(SecurityCheckComplete(Failure)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Refused)), Destroyed)
      case Local(SecurityCheckComplete(Resend)) =>
        OsmPair(Some(CheckSecurityRequirements), AcceptorWaitSecurityCheck)
      case Local(DisconnectReq) =>
        OsmPair(None, Destroyed)
      case Packet(DisconnectReq) =>
        OsmPair(Some(OsmAction.Seq([SendDisconnectRsp, AbortSecAccessReq])), Destroyed)
      case Packet(ConnectRsp(_, _)) | Packet(ConfigRsp(_)) | Packet(DisconnectRsp) | Packet(Data) | Local(WriteData) =>
        OsmPair(None, AcceptorWaitSecurityCheck)
      case Local(Timeout) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, AcceptorWaitSecurityCheck)
    }
  }

  // Current state: WaitLocalConnectResponse
  ghost function WaitLocalConnectResponseModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(Timeout) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Refused)), Destroyed)
      case Local(OpenChannelRsp(Success, CreditBased)) | Local(OpenChannelRsp(Success, Ble)) | Packet(PeerInfoRsp(Ble)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Success)), Open)
      case Local(OpenChannelRsp(Success, Classic)) | Packet(PeerInfoRsp(Classic)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Success)), Config)
      case Local(OpenChannelRsp(Pending, Classic)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Pending)), WaitLocalConnectResponse)
      case Local(OpenChannelRsp(Refused, _)) =>
        OsmPair(Some(SendConnectRsp(ConnectRspResult.Refused)), Destroyed)
      case Packet(ConnectRsp(_, _)) | Packet(ConfigRsp(_)) | Packet(DisconnectRsp) | Packet(Data) | Local(WriteData) =>
        OsmPair(None, WaitLocalConnectResponse)
      case Local(DisconnectReq) =>
        OsmPair(Some(SendDisconnectReq), WaitPeerDisconnectResponse)
      case Local(InternalFailure) | Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, WaitLocalConnectResponse)
    }
  }

  // Current state: Config
  ghost function ConfigModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Packet(ConfigRsp(Pending)) =>
        OsmPair(None, Config)
      case Packet(ConfigRsp(Success)) =>
        OsmPair(None, Open)
      case Packet(ConfigRsp(Reconfig))
        | Local(ConfigReq(Success))
        | Local(ConfigReq(Reconfig)) =>
        OsmPair(Some(SendConfigReq), Config)
      case Packet(ConfigRsp(Failure(true)))
        | Local(ConfigRsp(Failure(true)))
        | Local(Timeout) =>
        OsmPair(Some(SendDisconnectReq), Destroyed)
      case Packet(ConfigRsp(Failure(false)))
        | Local(ConfigRsp(Failure(false))) =>
        OsmPair(None, Destroyed)
      case Packet(ConfigReq(false))
        | Local(ConfigRsp(Reconfig)) =>
        OsmPair(Some(SendConfigRsp), Config)
      case Packet(DisconnectReq) =>
        OsmPair(None, WaitLocalDisconnectResponse)
      case Local(ConfigRsp(Success)) | Packet(ConfigReq(true)) =>
        OsmPair(Some(SendConfigRsp), Open)
      case Local(DisconnectReq) =>
        OsmPair(Some(SendDisconnectReq), WaitPeerDisconnectResponse)
      case Packet(Data) =>
        OsmPair(Some(ProcessPDU), Config)
      case Packet(DisconnectRsp) =>
        OsmPair(None, Config)
      case Local(WriteData) =>
        OsmPair(Some(SendData), Config)
      case Local(InternalFailure) | Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, Config)
    }
  }

  // Current state: Open
  ghost function OpenModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Packet(ConfigRsp(Success)) =>
        OsmPair(None, Open)
      case Packet(ConfigReq(_)) =>
        OsmPair(None, Open)
      case Local(ConfigReq(Success)) =>
        OsmPair(None, Config)
      case Local(ConfigRsp(Failure(true)))
        | Packet(Credit(true))
        | Local(Timeout) =>
        OsmPair(Some(SendDisconnectReq), Destroyed)
      case Local(ConfigRsp(Failure(false))) =>
        OsmPair(None, Destroyed)
      case Local(ConfigRsp(Reconfig)) =>
        OsmPair(Some(SendConfigRsp), Open)
      case Packet(DisconnectReq) =>
        OsmPair(None, WaitLocalDisconnectResponse)
      case Packet(Data) =>
        OsmPair(Some(ProcessPDU), Open)
      case Local(DisconnectReq) =>
        OsmPair(Some(SendDisconnectReq), WaitPeerDisconnectResponse)
      case Local(WriteData) =>
        OsmPair(Some(SendData), Open)
      case Local(ConfigReq(Reconfig)) =>
        OsmPair(Some(SendConfigReq), Config)
      case Local(SendCredit) | Packet(Credit(false)) | Packet(ConnectRsp(_, _)) | Packet(DisconnectRsp) =>
        OsmPair(None, Open)
      case Local(InternalFailure) | Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, Open)
    }
  }

  // Current state: WaitPeerDisconnectResponse
  ghost function WaitPeerDisconnectResponseModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Packet(DisconnectRsp) =>
        OsmPair(None, Destroyed)
      case Packet(DisconnectReq) =>
        OsmPair(Some(SendDisconnectRsp), Destroyed)
      case Local(WriteData) | Packet(Data) | Packet(ConnectRsp(_, _)) | Packet(ConfigRsp(_)) =>
        OsmPair(None, WaitPeerDisconnectResponse)
      case Packet(ConfigReq(_)) =>
        OsmPair(Some(SendCommandReject), WaitPeerDisconnectResponse)
      case Local(Timeout) | Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case _ =>
        OsmPair(None, WaitPeerDisconnectResponse)
    }
  }

  // Current state: WaitLocalDisconnectResponse
  ghost function WaitLocalDisconnectResponseModel(event: OsmEvent): OsmActionStatePair {
    match event {
      case Local(LinkDisconnectInd) =>
        OsmPair(None, Destroyed)
      case Local(Timeout)
        | Local(DisconnectReq)
        | Local(DisconnectRsp) =>
        OsmPair(Some(SendDisconnectRsp), Destroyed)
      case Local(WriteData) | Packet(Data) =>
        OsmPair(None, WaitLocalDisconnectResponse)
      case _ =>
        OsmPair(None, WaitLocalDisconnectResponse)
    }
  }
}
