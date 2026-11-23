module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftHomAffinePair

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_hom (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (hi : φ₀ ≫ D.i = D'.i ≫ φ) (p : Pair φ) :
    ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)),
      ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (CechDR.secPull D.s D'.s p a) := by
  let T' := Λ'.L.obj (Opposite.op p.1.1)
  let e' : Sec D'.s p.1.1.1 →+* T'.B := Λ'.e (Opposite.op p.1.1)
  let y₀ : Sec D.s p.1.2.1 →+* (m.obj T').B := e'.comp (CechDR.secPull D.s D'.s p)
  have hy : ∀ r : D.R, y₀ (algebraMap D.R _ r) = algebraMap D.R (m.obj T').B r := by
    intro r
    have h1 := semiHom_secPull hφ p r 1
    rw [map_one, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h1
    change e' (CechDR.secPull D.s D'.s p (algebraMap D.R _ r)) = algebraMap D'.R T'.B (σ r)
    rw [h1]
    exact (Λ'.e (Opposite.op p.1.1)).commutes _
  let y : Sec D.s p.1.2.1 →ₐ[D.R] (m.obj T').B := { y₀ with commutes' := hy }
  refine ((GlobalTheory.T.hom_spec_points_levels D Λ).1 (Opposite.op p.1.2) (m.obj T') y).1 ?_
  change spMap ((T'.π.comp e').comp (CechDR.secPull D.s D'.s p)) ≫ affPt D.s p.1.2 = (T'.x ≫ φ₀) ≫ D.i
  rw [Cris.spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, Category.assoc T'.x, hi, ← Category.assoc]
  exact congrArg (· ≫ φ) (Λ'.pt (Opposite.op p.1.1))

end GlobalTheory.PDForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftHomAffinePairStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_smoothLift_hom_affinePair : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ p : Pair φ, ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)), ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (secPull D.s D'.s p a) := by
  first | exact @GlobalTheory.PDForm.exists_lift_pair_hom | exact GlobalTheory.PDForm.exists_lift_pair_hom | (intros; apply GlobalTheory.PDForm.exists_lift_pair_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatTransLiftsOverAffinePairs

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_natTrans (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R)
    (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ)
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (hi : φ₀ ≫ D.i = D'.i ≫ φ) :
    ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a,
      (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
        Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  choose θ hθ using GlobalTheory.T.exists_smoothLift_hom_affinePair D D' Λ Λ' σ φ φ₀ hφ m hi
  refine ⟨⟨fun p ↦ θ p.unop, fun p q a ↦ ?_⟩, fun p a ↦ hθ p.unop a⟩
  apply Thick.Hom.ext'
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := (Λ.e (Opposite.op p.unop.1.2)).surjective b
  have h1 := Λ.nat ((pairSnd φ).map a) x
  have h2 := hθ q.unop (mp (OAff D.s) ((pairSnd φ).map a) x)
  have h3 := hθ p.unop x
  have h4 := Λ'.nat ((pairFst φ).map a) (GlobalTheory.CechDR.secPull D.s D'.s p.unop x)
  have h5 := (pairPull hφ).naturality a x
  exact ((congrArg (θ q.unop).φ h1.symm).trans h2).trans
    ((congrArg (Λ'.e (Opposite.op q.unop.1.1)) h5).trans
      (h4.trans (congrArg (Λ'.L.map ((pairFst φ).map a)).φ h3.symm)))

end GlobalTheory.PDForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatTransLiftsOverAffinePairsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  first | exact @GlobalTheory.PDForm.exists_lift_pair_natTrans | exact GlobalTheory.PDForm.exists_lift_pair_natTrans | (intros; apply GlobalTheory.PDForm.exists_lift_pair_natTrans <;> assumption)
end
end
