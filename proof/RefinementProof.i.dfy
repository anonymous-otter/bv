module RefinementProof {
  import opened CommonTypes

  import opened SpecStateMachine
  import opened OpsStateMachine

  // Check if SSM can transition from state s to state s' with respect to event e
  ghost predicate SsmNext(s: SsmState, s': SsmState, e: Option<SsmEventCondition>) {
    match e {
      case Some((e, c)) => ExecuteSsmModel(s, e, c).state == s'
      case None => s == s'
    }
  }

  // Check if OSM can transition from state s to state s' with respect to event e
  ghost predicate OsmNext(s: OsmState, s': OsmState, e: OsmEvent) {
    var model := ExecuteOsmModel(s, e);
    model.state == s'
  }

  /**
   * Abstraction functions of states, events, and actions from OSM to SSM
   */
  ghost function AbsState(s: OsmState, e: OsmEvent): SsmState {
    match s {
      case Created => Closed
      case Destroyed => Closed
      case InitiatorWaitSecurityCheck => Closed
      case AcceptorWaitSecurityCheck => Closed
      case WaitPeerConnectResponse => WaitConnectRsp
      case WaitLocalConnectResponse => WaitConnect
      case Config =>
        match e {
          case Packet(ConfigRsp(Success)) => SsmState.Config(WaitConfigRsp)
          case Local(ConfigRsp(Success)) => SsmState.Config(WaitControlInd)
          case Packet(ConfigReq(true)) => SsmState.Config(WaitConfigReq)
          case Local(ConfigReq(Success)) => SsmState.Config(WaitSendConfig)
          case Local(ConfigReq(Reconfig)) => SsmState.Config(WaitConfigReqRsp)
          case _ => SsmState.Config(WaitConfig)
        }
      case Open => SsmState.Open
      case WaitPeerDisconnectResponse => WaitDisconnect
      case WaitLocalDisconnectResponse => Closed
    }
  }

  ghost function AbsEvent(s: OsmState, e: OsmEvent): Option<SsmEventCondition> {
    match s {
      case Created =>
        match e {
          case Local(SecurityCheckComplete(Success(_, _)))
            => Some((Internal(AbstractEvent.OpenChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case _ => None
        }
      case InitiatorWaitSecurityCheck =>
        match e {
          case Local(SecurityCheckComplete(Success(_, _)))
            => Some((Internal(AbstractEvent.OpenChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case _ => None
        }
      case AcceptorWaitSecurityCheck =>
        match e {
          case Local(SecurityCheckComplete(Success(false, Classic)))
            => Some((Message(L2cap6Event.ConnectReq), SsmCondition(Standard, SsmStatus.Pending)))
          case Local(SecurityCheckComplete(Success(false, Ble)))
            => Some((Message(LeConnectReq), SsmCondition(Standard, SsmStatus.Pending)))
          case Local(SecurityCheckComplete(Success(_, CreditBased)))
            => Some((Message(LeConnectReq), SsmCondition(Standard, SsmStatus.Pending)))
          case Local(SecurityCheckComplete(Success(true, _)))
            => Some((Message(L2cap6Event.ConnectReq), SsmCondition(Standard, SsmStatus.Pending)))
          case _ => None
        }
      case WaitPeerConnectResponse =>
        match e {
          case Packet(ConnectRsp(Success, CreditBased)) | Packet(ConnectRsp(Success, Ble))
            => Some((Message(LeConnectRsp(SsmStatus.Success)), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(ConnectRsp(Success, Classic))
            => Some((Message(L2cap6Event.ConnectRsp(SsmStatus.Success)), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(ConnectRsp(Refused, Classic))
            => Some((Message(L2cap6Event.ConnectRsp(SsmStatus.Failure)), SsmCondition(Standard, SsmStatus.Failure)))
          case Packet(ConnectRsp(Refused, _))
            => Some((Message(LeConnectRsp(SsmStatus.Failure)), SsmCondition(Standard, SsmStatus.Failure)))
          case Packet(ConnectRsp(Pending, Classic))
            => Some((Message(L2cap6Event.ConnectRsp(SsmStatus.Pending)), SsmCondition(Standard, SsmStatus.Pending)))
          case Packet(ConnectRsp(Pending, _))
            => Some((Message(LeConnectRsp(SsmStatus.Pending)), SsmCondition(Standard, SsmStatus.Pending)))
          case Local(DisconnectReq)
            => Some((Internal(CloseChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case Local(Timeout) | Local(LinkDisconnectInd) | Local(InternalFailure)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case _ => None
        }
      case WaitLocalConnectResponse =>
        match e {
          case Local(OpenChannelRsp(Success, CreditBased)) | Local(OpenChannelRsp(Success, Ble)) | Packet(PeerInfoRsp(Ble))
            => Some((Internal(LeOpenChannelRsp), SsmCondition(Standard, SsmStatus.Success)))
          case Local(OpenChannelRsp(Success, Classic)) | Packet(PeerInfoRsp(Classic))
            => Some((Internal(AbstractEvent.OpenChannelRsp), SsmCondition(Standard, SsmStatus.Success)))
          case Local(OpenChannelRsp(Refused, Ble)) | Local(OpenChannelRsp(Refused, CreditBased))
            => Some((Internal(LeOpenChannelRsp), SsmCondition(Standard, SsmStatus.Failure)))
          case Local(OpenChannelRsp(Refused, Classic))
            => Some((Internal(AbstractEvent.OpenChannelRsp), SsmCondition(Standard, SsmStatus.Failure)))
          case Local(DisconnectReq)
            => Some((Internal(CloseChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case Local(Timeout) | Local(LinkDisconnectInd) | Local(InternalFailure)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case _ => None
        }
      case Config =>
        match e {
          case Packet(ConfigRsp(Success))
            => Some((Message(L2cap6Event.ConfigRsp(SsmStatus.Success)), SsmCondition(Standard, SsmStatus.Success)))
          case Local(ConfigRsp(Success))
            => Some((Internal(ControllerLogicalLinkInd), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(ConfigReq(true))
            => Some((Message(L2cap6Event.ConfigReq(ConfigOption.Unspecified)), SsmCondition(Standard, SsmStatus.Success)))
          case Local(DisconnectReq)
            => Some((Internal(CloseChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(ConfigRsp(Failure(_))) | Local(ConfigRsp(Failure(_))) | Local(Timeout) | Local(InternalFailure) | Local(LinkDisconnectInd)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case Packet(DisconnectReq)
            => Some((Message(L2cap6Event.DisconnectReq), SsmCondition(Standard, SsmStatus.Success)))
          case _ => None
        }
      case Open =>
        match e {
          case Local(ConfigReq(Success))
            => Some((Message(L2cap6Event.ConfigReq(ConfigOption.Unspecified)), SsmCondition(Standard, SsmStatus.Success)))
          case Local(ConfigReq(Reconfig))
            => Some((Internal(ReconfigureChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case Local(DisconnectReq)
            => Some((Internal(CloseChannelReq), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(Credit(true)) | Local(ConfigRsp(Failure(_))) | Local(Timeout) | Local(InternalFailure) | Local(LinkDisconnectInd)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case Packet(DisconnectReq)
            => Some((Message(L2cap6Event.DisconnectReq), SsmCondition(Standard, SsmStatus.Success)))
          case _ => None
        }
      case WaitPeerDisconnectResponse =>
        match e {
          case Packet(DisconnectRsp)
            => Some((Message(L2cap6Event.DisconnectRsp), SsmCondition(Standard, SsmStatus.Success)))
          case Packet(DisconnectReq)
            => Some((Message(L2cap6Event.DisconnectReq), SsmCondition(Standard, SsmStatus.Success)))
          case Local(Timeout) | Local(LinkDisconnectInd)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case _ => None
        }
      case WaitLocalDisconnectResponse =>
        match e {
          case Local(Timeout) | Local(LinkDisconnectInd)
            => Some((Internal(AbstractEvent.Error), SsmCondition(Standard, SsmStatus.Failure)))
          case Packet(Data)
            => Some((Message(L2cap6Event.Data(Default)), SsmCondition(Standard, SsmStatus.Success)))
          case _ => None
        }
      case _ => None
    }
  }

  // Lemma to prove refinement: OSM transitions refine SSM transitions
  lemma OsmRefinesSsm(s: OsmState, s': OsmState, e: OsmEvent)
    requires OsmNext(s, s', e)
    ensures SsmNext(AbsState(s, e), AbsState(s', e), AbsEvent(s, e))
  {}
}