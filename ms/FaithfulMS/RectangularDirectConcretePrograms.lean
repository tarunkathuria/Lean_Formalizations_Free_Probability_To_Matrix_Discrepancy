import FaithfulMS.RectangularDirectConcreteResponse
import FaithfulMS.RectangularDirectConcreteAcceptance

/-! All local implementation obligations are discharged here. The only
remaining input is the permitted primal-SDP service with its work contract.
Invariants are proof arguments: off-domain totalization of a response is not
an additional runtime test. The walk invokes it only on certified states. -/
noncomputable section
namespace MatrixSpencer.RectangularDirectConcretePrograms
open FaithfulMS

def programs (S : DirectSDP.PolynomialService) : RectangularDirectPrograms.Programs S where
  response := RectangularDirectConcreteResponse.response S
  response_value := RectangularDirectConcreteResponse.response_value S
  responseBudget := RectangularDirectConcreteResponse.budget S
  response_cost := RectangularDirectConcreteResponse.response_cost S
  response_polynomial := RectangularDirectConcreteResponse.budget_polynomial S
  accepts := RectangularDirectConcreteAcceptance.accepts S
  accepts_value := RectangularDirectConcreteAcceptance.accepts_value S
  acceptanceBudget := RectangularDirectConcreteAcceptance.acceptanceBudget S
  accepts_cost := RectangularDirectConcreteAcceptance.accepts_cost S
  acceptance_polynomial := RectangularDirectConcreteAcceptance.acceptanceBudget_polynomial S

end MatrixSpencer.RectangularDirectConcretePrograms
