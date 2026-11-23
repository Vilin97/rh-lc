module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachLift
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigBasis
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasselmanWallachAdmissible
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeRepresentation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.E3D
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonal
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsFunctional
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HighestWeightKernel
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionLinear
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PageTheorem
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SeminormApproximation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZeroOnDense
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZetaClassicalZeroFreeRegion

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C

section

@[expose] public section

namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C7

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.D5

section

@[expose] public section

namespace PositivityTheory.CW

theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.Imports

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped ComplexOrder

namespace PositivityTheory.CW

theorem c5 : C5 := by
  intro n ε H _ _ _ σ hU hI
  have hHC := CompanionTheory.D.gk.HC.print_harishChandraModules
  refine ⟨fun v hv => GlobalTheory.CWGeneral.sm_of_isKFin hHC hU hI hv,
    fun v hv X hX => GlobalTheory.CWGeneral.isKFin_dRep_of_irred hHC hU hI hv hX, fun w hw S hS δ hδ => ?_⟩
  have hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ := ⟨hU.1.1, hU.1.2, hU.2.1, hU.2.2⟩
  have hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
    have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
      ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
    refine ⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩
    · rw [hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    · rw [Formalism.REAL.Jm_mul_self]; exact Matrix.PosDef.one
  set δ' : ℝ := δ / (S.length + 1) with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by positivity)
  obtain ⟨v, hvS, hvK, hvw⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w
    hw S hS δ' hδ'0
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨W, hW, hvW, hst⟩ := hvK
    refine ⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩
    show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]
  · have hv' : Sm ε σ v := hvS
    have key : ∀ l ∈ S, ‖Dw σ l (w - v)‖ ≤ δ' := by
      intro l hl
      have e : Dw σ l (w - v) = Dw σ l w - Dw σ l v := by
        have := Dw_add hU (hS l hl) (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hv'))) hv'
        rw [sub_add_cancel] at this
        rw [this, add_sub_cancel_right]
      rw [e, norm_sub_rev]
      exact (hvw l hl).le
    have hL : (S.length : ℝ) * δ' < δ := by
      rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    delta sobNorm
    calc (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).sum
        ≤ (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).length • δ' :=
          List.sum_le_length_nsmul _ _ (fun x hx => by
            obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
            exact key l hl)
      _ = S.length * δ' := by simp
      _ < δ := hL

end PositivityTheory.CW
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CwOf

section

@[expose] public section

namespace PositivityTheory.CW

theorem lift_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallachLift := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact lift_of_steps hM hmodel c4 c5 c6 c7 d0 d1b d2 d3 d4b d5

theorem cw_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallach := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact cw_of_steps hM hmodel c5 d0 (lift_of hM) e1a e1b e2a e2b e2c e2d e3a e3b e3c e3d

end PositivityTheory.CW
end
end
