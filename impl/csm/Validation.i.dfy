
module Impl.Csm.Validation {
  import opened CommonTypes
  import opened Types

  import opened L2cCsmOsm
  import opened OpsStateMachine

  ghost predicate IsValidStateMachine(csm: L2cCsm, p_ccb: tL2C_CCB)
    reads csm, p_ccb
  {
    && p_ccb.external_event.None?
    && csm.model.state == OpsState(p_ccb)
    && csm.model.action == OpsAction(csm.footprint)
    && HaveActionsHappened(csm.model.action)
  }

  ghost function OpsState(p_ccb: tL2C_CCB): OsmState
    reads p_ccb
  {
    if p_ccb.IsDestroyed() then
      Destroyed
    else
      match p_ccb.chnl_state {
        case CST_CLOSED => Created
        case CST_ORIG_W4_SEC_COMP => InitiatorWaitSecurityCheck
        case CST_W4_L2CAP_CONNECT_RSP => WaitPeerConnectResponse
        case CST_TERM_W4_SEC_COMP => AcceptorWaitSecurityCheck
        case CST_W4_L2CA_CONNECT_RSP => WaitLocalConnectResponse
        case CST_W4_L2CAP_DISCONNECT_RSP => WaitPeerDisconnectResponse
        case CST_W4_L2CA_DISCONNECT_RSP => WaitLocalDisconnectResponse
        case CST_CONFIG => Config
        case CST_OPEN => Open
      }
  }

  ghost function OpsAction(action: seq<ImplAction>): seq<OsmAction> {
    if |action| == 0 then [] else
    match action[0] {
      case SendConnectReq => [OsmAction.SendConnectReq] + OpsAction(action[1..])
      case SendConnectRsp(result) => [OsmAction.SendConnectRsp(result)] + OpsAction(action[1..])
      case SendConfigReq => [OsmAction.SendConfigReq] + OpsAction(action[1..])
      case SendConfigRsp => [OsmAction.SendConfigRsp] + OpsAction(action[1..])
      case SendCommandReject => [OsmAction.SendCommandReject] + OpsAction(action[1..])
      case SendDisconnectReq => [OsmAction.SendDisconnectReq] + OpsAction(action[1..])
      case SendDisconnectRsp => [OsmAction.SendDisconnectRsp] + OpsAction(action[1..])
      case CheckSecurityRequirements => [OsmAction.CheckSecurityRequirements] + OpsAction(action[1..])
      case AbortSecAccessReq => [OsmAction.AbortSecAccessReq] + OpsAction(action[1..])
      case ProcessPDU => [OsmAction.ProcessPDU] + OpsAction(action[1..])
      case SendData => [OsmAction.SendData] + OpsAction(action[1..])
    }
  }

  ghost predicate HaveActionsHappened(actions: seq<OsmAction>) {
    forall i: int :: 0 <= i < |actions|
                     ==> match actions[i] {
                         case CheckSecurityRequirements => IsSecAccessReqSent()
                         case AbortSecAccessReq => IsSecAbortReqSent()
                         case SendConnectReq => IsPeerConnectReqSent()
                         case SendConnectRsp(_) => IsPeerConnectRspSent()
                         case SendDisconnectReq => IsPeerDisconnectReqSent()
                         case SendDisconnectRsp => IsPeerDisconnectRspSent()
                         case SendConfigReq => IsPeerConfigReqSent()
                         case SendConfigRsp => IsPeerConfigRspSent()
                         case ProcessPDU => IsPDUProcessed()
                         case SendData => IsDataSent()
                         case SendCommandReject | Seq(_) => true // no effect
                       }
  }

  ghost method {:axiom} ExecuteAndAssumeSideEffects(csm: L2cCsm, expected_current: OsmState, event: OsmEvent, p_ccb: tL2C_CCB)
    requires csm.model.state == expected_current
    modifies csm`model, csm`footprint
    ensures csm.model == match ExecuteOsmModel(old(csm.model.state), event) {
                           case OsmPair(action, state) => L2cCsmModel(state, csm.ToActionSeq(action))
                         }
    ensures OpsAction(csm.footprint) == csm.model.action
    ensures HaveActionsHappened(csm.model.action)
    ensures csm.IsDestroyedState() ==> p_ccb.IsDestroyed()
  {
    // Simulate execution of the event
    var exe_result := ExecuteOsmModel(csm.model.state, event);
    var exe_result_action := csm.ToActionSeq(exe_result.action);

    // Make sure it is consistent with csm
    csm.Execute(event);
    assert csm.model.state == exe_result.state;
    assert |csm.model.action| >= |exe_result_action|;
    assert forall i :: 0 <= i < |exe_result_action| ==> exe_result_action[i] == csm.model.action[(|csm.model.action| - |exe_result_action| + i)];

    // Then we assume all the expected things (side effects) have happened
    assume OpsAction(csm.footprint) == csm.model.action;
    assume HaveActionsHappened(csm.model.action);
    if csm.IsDestroyedState() {
      assume p_ccb.IsDestroyed();
    }
  }
}
