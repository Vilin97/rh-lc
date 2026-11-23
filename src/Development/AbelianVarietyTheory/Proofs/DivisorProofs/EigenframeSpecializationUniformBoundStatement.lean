module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

theorem tendsto_of_inv_mulVec_span {α : Type} {l : Filter α} {N n : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ)
    (u : Fin n → Fin N → ℂ) (L : Fin n → Fin N → ℂ) (hdet : ∀ᶠ w in l, (M w).det ≠ 0)
    (ht : ∀ j, Tendsto (fun w => Matrix.mulVec (M w)⁻¹ (u j)) l (𝓝 (L j)))
    (hs : Submodule.span ℂ (Set.range L) = ⊤) : ∃ L0, Tendsto M l (𝓝 L0) := by
  have hc : ∀ a : Fin N, ∃ c : Fin n → ℂ, ∑ j, c j • L j = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose c hc using hc
  let W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun b a => ∑ j, c a j * u j b
  have hR : Tendsto (fun w => (M w)⁻¹ * W) l (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a' => tendsto_pi_nhds.2 fun a => ?_
    have e : ∀ w, ((M w)⁻¹ * W) a' a = ∑ j, c a j * (Matrix.mulVec (M w)⁻¹ (u j)) a' := by
      intro w
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
    have lim : (1 : Matrix (Fin N) (Fin N) ℂ) a' a = ∑ j, c a j * L j a' := by
      have := congrFun (hc a) a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Pi.single_apply, Matrix.one_apply]
    simp only [e]
    rw [lim]
    exact tendsto_finsetSum _ fun j _ => ((ht j).apply_nhds a').const_mul _
  have hRi : Tendsto (fun w => ((M w)⁻¹ * W)⁻¹) l (𝓝 1) := by
    have h0 : ContinuousAt Ring.inverse (1 : Matrix (Fin N) (Fin N) ℂ).det := by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h1 := ((continuousAt_matrix_inv (1 : Matrix (Fin N) (Fin N) ℂ) h0).tendsto).comp hR
    rw [inv_one] at h1
    exact h1
  have hRd : ∀ᶠ w in l, ((M w)⁻¹ * W).det ≠ 0 := by
    have h1 : Tendsto (fun w => ((M w)⁻¹ * W).det) l (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin N) (Fin N) ℂ)).comp hR
    rw [Matrix.det_one] at h1
    exact h1.eventually_ne one_ne_zero
  refine ⟨W, ?_⟩
  have hlim : Tendsto (fun w => W * ((M w)⁻¹ * W)⁻¹) l (𝓝 (W * 1)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hRi
  rw [Matrix.mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdet, hRd] with w h1 h2
  have e1 : M w * ((M w)⁻¹ * W) = W := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.one_mul]
  calc W * ((M w)⁻¹ * W)⁻¹ = M w * ((M w)⁻¹ * W) * ((M w)⁻¹ * W)⁻¹ := by rw [e1]
    _ = M w := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2), Matrix.mul_one]

theorem periods_bounded_outside_cmType_of_definite_arc_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift hp0 v
  obtain ⟨n, vv, Lp, Lm, hLp, -, hsp⟩ := GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x
    fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  have hdom : ∀ᶠ w in imTop, xx w ∈ (U.X k).dom := by
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)] with w hw
    exact horb.2.2.2.1 w hw
  have hmat : ∀ τ' : (U.X k).Ψ, ∃ L0, Tendsto (fun w => mat (xx w) τ') imTop (𝓝 L0) := by
    intro τ'
    refine tendsto_of_inv_mulVec_span (fun w => mat (xx w) τ') (fun j => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 (vv j))
      (fun j i => Lp j τ' ⟨i, by omega⟩) ?_ ?_ ?_
    · filter_upwards [hdom] with w hw
      exact (hw τ').1
    · intro j
      refine tendsto_pi_nhds.2 fun i => ?_
      have hi : (i : ℕ) < N - (U.X k).p0 := by omega
      refine (hLp j τ' ⟨i, hi⟩).congr fun w => ?_
      unfold perFr
      rw [dite_eq_left τ'.2, dite_eq_left (by simp only [hp0]; omega)]
      congr 1
      ext
      simp [hp0]
    · exact span_proj (fun j => Lp j τ') (hsp τ').1 (fun i => ⟨i, by omega⟩)
        (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  choose L0 hL0 using hmat
  let F : ℂ → ((U.X k).Ψ → Fin N → ℂ) := fun w τ' a =>
    ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (mat (xx w) τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v)
  have hF : Tendsto F imTop (𝓝 (fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v))) := by
    refine tendsto_pi_nhds.2 fun τ' => tendsto_pi_nhds.2 fun a => ?_
    have hc : Continuous fun Mx : Matrix (Fin N) (Fin N) ℂ =>
        ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col Mx a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.hermC col
      fun_prop
    exact (hc.tendsto _).comp (hL0 τ')
  refine ⟨‖(fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) :
      (U.X k).Ψ → Fin N → ℂ)‖ + 1, ?_⟩
  filter_upwards [hF.norm.eventually (gt_mem_nhds (lt_add_one _))] with w hw
  intro τ i hτ
  unfold perFr
  rw [dite_eq_right hτ]
  split_ifs with h' hj
  · exact ((norm_le_pi_norm (F w ⟨_, h'⟩) ⟨_, hj⟩).trans (norm_le_pi_norm (F w) ⟨_, h'⟩)).trans hw.le
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

end GlobalTheory.ShFam.PerLim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLiftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)


theorem _root_.GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  first | exact @GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | exact GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | (intros; apply GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArcStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)


theorem _root_.GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ v ∈ (U.X k).Λ, ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice | exact GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice | (intros; apply GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerFurther

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {N : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E N) (v : Fin N → E),
    ∃ (n : ℕ),
      (0 : ℕ) < n ∧
        (↑n : E) • v ∈
          X.Λ := by
  intro E _ _ _ N X v
  refine Submodule.span_induction (fun x hx => ⟨1, one_pos, by simpa using hx⟩) ⟨1, one_pos, by simp⟩
    ?_ ?_ (X.Λ_span ▸ Submodule.mem_top : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    convert X.Λ.add_mem (nsmul_mem hx b) (nsmul_mem hy a) using 1
    ext i; simp; ring
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨m, s, hm, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ c)).exists_nsmul_eq (NumberField.RingOfIntegers E)
    refine ⟨m * a, mul_pos (Nat.pos_of_ne_zero hm) ha, ?_⟩
    convert X.Λ.smul_mem s hx using 1
    rw [← algebraMap_smul E s, ← hs]; ext i; simp; ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.PerPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_nat_smul_mem {N : ℕ} (X : Data E N) (v : Fin N → E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem X v

theorem perFr_natCast_smul {N : ℕ} (X : Data E N) (x : Frame X.Ψ N) (v : Fin N → E) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x ((n : E) • v) τ i = (n : ℂ) * perFr X x v τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ ((n : E) • v) = (n : ℂ) • Data.emb τ v := fun τ => funext fun a => by
    simp [Data.emb, map_natCast]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v R
  obtain ⟨n, hn, hnv⟩ := exists_nat_smul_mem (U.X k) v
  obtain ⟨C₁, B, h₁⟩ := GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
    _ hnv R
  obtain ⟨C₃, h₃⟩ : ∃ C₃ : ℝ, ∀ᶠ w in imTop, (U.X k).p0 = 0 → ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := by
    by_cases h0 : (U.X k).p0 = 0
    · obtain ⟨C₃, h⟩ := GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
        h0 v
      exact ⟨C₃, h.mono fun w hw _ => hw⟩
    · exact ⟨0, .of_forall fun w h => absurd h h0⟩
  have him : ∀ᶠ w in imTop, 1 ≤ w.im :=
    (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_ge_atTop 1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨max (C₁ / n) 0 + max C₃ 0, B, ?_⟩
  filter_upwards [h₁, h₃, him] with w hw1 hw3 hwi hR τ i
  have hpow : 1 ≤ w.im ^ B := one_le_pow₀ hwi
  have hK0 : 0 ≤ max (C₁ / n) 0 + max C₃ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hK1 : C₁ / n ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hK3 : C₃ ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hlat : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := by
    intro τ i h
    have h2 := hw1 hR τ i h
    rw [perFr_natCast_smul, norm_mul, Complex.norm_natCast] at h2
    have h3 : ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₁ / n * w.im ^ B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn']
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have hzero : 0 ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := mul_nonneg hK0 (by positivity)
  by_cases hτ : τ ∈ (U.X k).Ψ
  · by_cases hi : i < N - (U.X k).p0
    · exact hlat τ i (Or.inl ⟨hτ, hi⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_left hτ, dite_eq_right (by omega)]
      rw [e, norm_zero]
      exact hzero
  · by_cases hc : conjEmb τ ∈ (U.X k).Ψ
    · by_cases h0 : (U.X k).p0 = 0
      · calc ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := hw3 h0 τ i hτ
          _ ≤ max (C₁ / n) 0 + max C₃ 0 := hK3
          _ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := le_mul_of_one_le_right hK0 hpow
      · by_cases hi : i < (U.X k).p0
        · exact hlat τ i (Or.inr ⟨hc, hi⟩)
        · have e : perFr (U.X k) (xx w) v τ i = perFr (U.X k) (xx w) v τ ((U.X k).p0 - 1) := by
            have e1 : (U.X k).p0 - 1 - i = (U.X k).p0 - 1 - ((U.X k).p0 - 1) := by omega
            unfold perFr
            rw [dite_eq_right hτ, dite_eq_right hτ, dite_eq_left hc, dite_eq_left hc]
            simp only [e1]
          rw [e]
          exact hlat τ _ (Or.inr ⟨hc, by omega⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_right hτ, dite_eq_right hc]
      rw [e, norm_zero]
      exact hzero

end GlobalTheory.ShFam.PerPoly
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.eigenframe_specialization_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.ShFam.PerPoly.periods_le_pow | exact GlobalTheory.ShFam.PerPoly.periods_le_pow | (intros; apply GlobalTheory.ShFam.PerPoly.periods_le_pow <;> assumption)
end
end
