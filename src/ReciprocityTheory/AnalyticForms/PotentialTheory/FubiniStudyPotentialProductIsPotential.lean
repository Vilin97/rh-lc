import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint CompatibleChartOperations

noncomputable section

section ProdChart

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)

end ProdChart

section ProdChart2

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

end ProdChart2

section Pull

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

end Pull

open scoped Classical in

open scoped Classical in

def diagSec (x y : OnePoint ℂ × OnePoint ℂ) : ℂ :=
  if x.1 = ∞ then
    (if x.2 = ∞ then crd1 y.1 - crd1 y.2 else crd1 y.1 * crd0 y.2 - 1)
  else
    (if x.2 = ∞ then 1 - crd0 y.1 * crd1 y.2 else crd0 y.2 - crd0 y.1)

end

end ReciprocityTheory.AnForm.M
