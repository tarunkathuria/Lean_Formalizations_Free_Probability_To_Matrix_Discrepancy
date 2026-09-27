import FaithfulMS.DirectSDP

/-! An instance adapter for the one explicit generic exact SDP service.
It provides no covariance derivative, supporting plane, or walk condition. -/
namespace FaithfulMS.SquareDirectOracle
class Oracle where
  service : FaithfulMS.DirectSDP.Service
end FaithfulMS.SquareDirectOracle
