import Tools.S1LoadReview.External

/-! Tooling control. Consumer: Local.lean. Reach: multiple-root module accounting only. -/
namespace S1LoadReview.Peer
theorem peerTop : True := S1LoadReview.External.sharedJoint
end S1LoadReview.Peer
