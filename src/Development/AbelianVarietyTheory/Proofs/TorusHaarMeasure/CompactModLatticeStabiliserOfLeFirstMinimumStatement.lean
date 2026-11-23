module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsCompactOrthBounded

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.OrthFrameMahler

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c

theorem norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by
  have h1 : rmul z t τ a c = z τ a c * t τ c c := by
    show ∑ k, z τ a k * t τ k c = _
    refine Finset.sum_eq_single c (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ c) h)
    rw [(hdiag τ k).2 c (Ne.symm hk), mul_zero]
  calc ‖z τ a c‖ = ‖rmul z t τ a c‖ := by
        rw [h1, norm_mul, (hdiag τ c).1, mul_one]
    _ ≤ ‖rmul z t τ a‖ := norm_le_pi_norm _ c
    _ ≤ ‖rmul z t τ‖ := norm_le_pi_norm _ a
    _ ≤ ‖rmul z t‖ := norm_le_pi_norm _ τ

theorem exists_bound_orthonormal_frame :
    (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x →
      ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  intro r X ε hε
  obtain ⟨K, hKc, hKd, hK⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨β, hβc, hβ⟩ := GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt (E := E) r X
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (continuousOn_rmul_self (hβc.mono hKd))
  refine ⟨R, fun x hx hla => ?_⟩
  obtain ⟨γ, hγ, b, hb, hy⟩ := hK x (IW.orth_mem_dom X x hx) hla
  refine ⟨γ, X.Γ_stab γ hγ, fun τ a c => ?_⟩
  obtain ⟨hβb, hβo⟩ := hβ _ (hKd hy)
  have hRy : ‖rmul (lact γ (rmul x b)) (β (lact γ (rmul x b)))‖ ≤ R := hR _ hy
  generalize β (lact γ (rmul x b)) = s at hβb hβo hRy
  rw [FundSetPf.lact_rmul, ExtFPf.rmul_assoc] at hβo hRy
  have hγo : IsOrth X (lact γ x) := fun σ => by rw [OntoS.gram_lact X hγ]; exact hx σ
  have hdiag := (GlobalTheory.isOrth_rmul_iff_unitary_diagonal r X _ _ hγo (ExtFPf.mul_mem X hb hβb)).1 hβo
  exact (norm_apply_le_of_diagonal _ _ hdiag τ a c).trans hRy

end GlobalTheory.OrthFrameMahler
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahlerStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_bound_orthonormal_frame_mahler : (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x → ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  first | exact @GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | exact GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | (intros; apply GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

end GlobalTheory.FiniteCovolume
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitaryStab_mul_compact_of_le_firstMinimum :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_bound_orthonormal_frame_mahler r X ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (GlobalTheory.FinCovol.isCompact_orth_bounded r X R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

end GlobalTheory.FiniteCovolume
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimumStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | exact GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum | (intros; apply GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum <;> assumption)
end
end
