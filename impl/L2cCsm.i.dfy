module L2cCsmOsm {
  import opened CommonTypes

  import opened OpsStateMachine

  // The action to represent function calls in the L2CAP state machine implementation
  datatype ImplAction =
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

  // The model of L2CAP channel state machine using OpsStateMachine
  datatype L2cCsmModel = L2cCsmModel(state: OsmState, action: seq<OsmAction>)

  class L2cCsm {
    ghost var model: L2cCsmModel
    ghost var footprint: seq<ImplAction> // actual action history, to prove equivalence with action from model
    ghost var no_retry: bool // assume that we can only retry once in the event of L2CEVT_LP_DISCONNECT_IND in CST_W4_L2CAP_CONNECT_RSP state

    ghost predicate IsDestroyedState()
      reads this`model
    {
      model.state == Destroyed
    }

    constructor InitStateMachine()
      ensures model.state == Created
      ensures model.action == []
      ensures footprint == []
      ensures !no_retry
    {
      model := L2cCsmModel(Created, []);
      footprint := [];
      no_retry := false;
    }

    ghost method Execute(event: OsmEvent)
      modifies this`model, this`footprint
      ensures model == match ExecuteOsmModel(old(model.state), event) {
                         case OsmPair(action, state) => L2cCsmModel(state, ToActionSeq(action))
                       }
      ensures footprint == []
    {
      var next := ExecuteOsmModel(model.state, event);
      model := L2cCsmModel(next.state, ToActionSeq(next.action));
      footprint := [];
    }

    ghost method Retry()
      requires !no_retry
      requires model.state == Destroyed
      modifies this`model, this`no_retry, this`footprint
      ensures model.state == Created
      ensures model.action == []
      ensures footprint == []
      ensures no_retry
    {
      no_retry := true;
      model := L2cCsmModel(Created, []);
      footprint := [];
    }

    // TODO: #144
    ghost function ToActionSeq(action: Option<OsmAction>): seq<OsmAction> {
      match action {
        case None => []
        case Some(Seq(seq0)) => seq0
        case Some(x) => [x]
      }
    }

  }

  /**
    * The following predicates are used to verify the side effect of actions.
    */

  ghost predicate {:axiom} IsChannelReleased()

  ghost predicate {:axiom} IsSecAccessReqSent()

  ghost predicate {:axiom} IsSecAbortReqSent()

  ghost predicate {:axiom} IsPeerConnectReqSent()

  ghost predicate {:axiom} IsPeerConnectRspSent()

  ghost predicate {:axiom} IsPeerDisconnectReqSent()

  ghost predicate {:axiom} IsPeerDisconnectRspSent()

  ghost predicate {:axiom} IsPeerConfigReqSent()

  ghost predicate {:axiom} IsPeerConfigRspSent()

  ghost predicate {:axiom} IsPDUProcessed()

  ghost predicate {:axiom} IsDataSent()
}
