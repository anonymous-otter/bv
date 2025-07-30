module Impl.Csm.W4L2capDisconnectRsp {
  import opened Types
  import opened External.Logging
  import opened Utils

  import opened OpsStateMachine
  import opened L2cCsmOsm
  import opened Validation
  import opened L2cCsmExtern

  type DataPossibleView<T> = AbsTypes.DataPossibleView<T>

  method l2c_csm_w4_l2cap_disconnect_rsp(ghost csm: L2cCsm, p_ccb: tL2C_CCB, event: tL2CEVT, p_data: DataPossibleView<IgnorableData>)
    // Base Assumptions
    requires && p_ccb.IsInState(CST_W4_L2CAP_DISCONNECT_RSP)
             && p_ccb.p_lcb_o != null
    modifies p_ccb.p_lcb_o
    modifies p_ccb`p_lcb_o
    // functionality specifications
    requires match event {
               case
                 | L2CEVT_L2CAP_DATA
                 | L2CEVT_L2CA_DATA_WRITE => true
               case _ => false
             }
             ==> p_data.View?
    // state machine specifications
    requires !csm.IsDestroyedState()
    requires IsValidStateMachine(csm, p_ccb)
    modifies csm
    ensures IsValidStateMachine(csm, p_ccb)
  {
    log_csm_execution_start("W4L2capDisconnectRsp", CST_W4_L2CAP_DISCONNECT_RSP, event, p_ccb);

    csm.Execute(OpsEvent(event, p_ccb));

    match (event) {
      case L2CEVT_L2CAP_DISCONNECT_RSP /* Peer disconnect response */ =>
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_L2CAP_DISCONNECT_REQ /* Peer disconnect request  */ =>
        l2cu_send_peer_disc_rsp(csm, p_ccb.p_lcb_o.GetExternalHandle(), p_ccb.remote_id(), p_ccb.local_cid(),
                                p_ccb.remote_cid);
        l2cu_release_ccb(csm, p_ccb.GetExternalHandle());

      case L2CEVT_LP_DISCONNECT_IND /* Link was disconnected */
        | L2CEVT_TIMEOUT           /* Timeout */ =>
        l2cu_release_ccb(csm,p_ccb.GetExternalHandle());

      case L2CEVT_L2CAP_DATA     /* Peer data packet rcvd    */
        | L2CEVT_L2CA_DATA_WRITE /* Upper layer data to send */ =>
        l2c_csm_osi_free(p_data.view);

      case _ =>
        log("W4L2capDisconnectRsp", LogLevel.Error, "Handling unexpected event: " + l2c_csm_get_event_name(event));
    }

    log_csm_execution_exit("W4L2capDisconnectRsp", p_ccb.chnl_state, event);
  }

  ghost function OpsEvent(event: tL2CEVT, p_ccb: tL2C_CCB): OsmEvent {
    match event {
      case L2CEVT_L2CAP_DISCONNECT_RSP =>
        Packet(PacketEvent.DisconnectRsp)
      case L2CEVT_L2CAP_DISCONNECT_REQ =>
        Packet(PacketEvent.DisconnectReq)
      case L2CEVT_LP_DISCONNECT_IND =>
        Local(LinkDisconnectInd)
      case L2CEVT_TIMEOUT =>
        Local(Timeout)
      case L2CEVT_L2CA_DATA_WRITE =>
        Local(WriteData)
      case L2CEVT_L2CAP_DATA =>
        Packet(Data)
      case _ =>
        Unmodeled
    }
  }
}
