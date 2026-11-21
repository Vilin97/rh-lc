import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
import Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
import Mathlib
import Formalism.IncomingBounds.LevelTail
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco

namespace Formalism.IncomingBounds

theorem lemmaFa : LemmaFa := strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
theorem cayleyId : CayleyId := cayleyIdentity

end Formalism.IncomingBounds
