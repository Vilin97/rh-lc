module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

end GlobalTheory.AdeleEv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlace

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

theorem norm_ev_intAf_le {i : E →+* PadicAlgCl l} {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (h : EvOk i ev)
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm z)‖ ≤ 1 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
    · rw [Algebra.TensorProduct.comm_symm_tmul, h.1]
      exact GlobalTheory.AdeleEv.norm_int_le i b
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      exact h.2.1 _ y.2
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

end Int

end GlobalTheory.FrameOf

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem incOf_mem_range {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) (x : D.host.E) :
    incOf D e0 b τ x ∈ Set.range e0 := by
  cases b
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem kapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : KapAt p j P w := by
  intro _ e0 b ev rk _ hev
  obtain ⟨y, hy⟩ := exists_levInt p j (p.R.mu w)
  refine ⟨fun _ => 1, fun _ => rfl, fun κ τ a c => ?_⟩
  have hk : kapMat p j (p.R.mu w) ev (fun _ => 1) rk κ τ a c = ev τ (matOf j κ.1 (rk a) (rk c)) := by
    simp [kapMat, Matrix.submatrix_apply, Matrix.map_apply]
  rw [hk]
  refine ⟨?_, ?_⟩
  · refine IntermediateField.adjoin.mono _ _ _ ?_ ((hev τ).2.2.2 _)
    rintro _ ⟨x, rfl⟩
    exact incOf_mem_range e0 b τ x
  · have hz : Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← hy κ (rk a) (rk c)]
      exact ((y κ).val (rk a) (rk c)).2
    have h := norm_ev_intAf_le (hev τ) _ hz
    have he : (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
        (Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c))) = matOf j κ.1 (rk a) (rk c) :=
      (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm_apply_apply _
    rwa [he] at h

end Pt

end GlobalTheory.FrameOf
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]
end Int
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pt
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem kapSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ _ _ p _ _ j P _ _ _ w _ _ _ => kapAt p j P w⟩⟩⟩
end Pt
end GlobalTheory.FrameOf
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inRange_kapAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @_root_.GlobalTheory.FrameOf.kapSt_alt | exact _root_.GlobalTheory.FrameOf.kapSt_alt | (intros; apply _root_.GlobalTheory.FrameOf.kapSt_alt <;> assumption)
end
end
end
