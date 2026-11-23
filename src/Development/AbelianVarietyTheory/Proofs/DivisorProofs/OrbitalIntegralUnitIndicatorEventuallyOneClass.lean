module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignKernelCharFactorConjInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductio
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  first | exact @GlobalTheory.CptCent.cptPart_le_conj_KL | exact GlobalTheory.CptCent.cptPart_le_conj_KL | (intros; apply GlobalTheory.CptCent.cptPart_le_conj_KL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOne

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.KapSignFull

theorem ordL_cj_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (hcj : ∀ x, Valued.v (cj w x) = Valued.v x) (x : w.adicCompletion E) (hx : x ≠ 0) :
    ordL (cj w x * x) = 2 * ordL x := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have e : Valued.v (cj w x * x) = Valued.v x * Valued.v x := by rw [map_mul, hcj]
  have h1 : Valued.v (cj w x * x) ≠ 0 := by rw [e]; exact mul_ne_zero h0 h0
  unfold ordL
  rw [dite_eq_right h1, dite_eq_right h0]
  have : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]
  rw [this, toAdd_mul]; ring

theorem kapSign_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  intro E _ _ _ n w hcj γ
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only []
    set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV
    have htop : V₁ = ⊤ := by rw [hV, Matrix.aeval_self_charpoly]; simp
    set b := Module.finBasis (w.adicCompletion E) V₁
    have hm : Module.finrank (w.adicCompletion E) V₁ = n := by
      rw [htop, finrank_top]; simp
    let e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n := finCongr hm
    let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := fun k j => (b (e.symm j)).1 k
    have hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) =
        ((M.map (cj w))ᵀ * M).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    have hM : M.det ≠ 0 := by
      have hli : LinearIndependent (w.adicCompletion E) M.col := by
        have h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) :=
          b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
        have h2 := h1.comp e.symm e.symm.injective
        have hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm := by funext j; rfl
        rw [hc]; exact h2
      exact (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero
    rw [hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl,
      ordL_cj_mul w hcj _ hM]
    exact Even.neg_one_zpow ⟨ordL M.det, by ring⟩

end GlobalTheory.BCT.KapSignFull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localSign_full_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  first | exact @GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | exact GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | (intros; apply GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductioStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  first | exact @GlobalTheory.BCT.kapSign_eq_one_of_integral | exact GlobalTheory.BCT.kapSign_eq_one_of_integral | (intros; apply GlobalTheory.BCT.kapSign_eq_one_of_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.OrbUnit
open DoubleCoset

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have h1 : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [h1, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun a => Subsingleton.elim _ _⟩
  rw [finsum_unique]
  simp

theorem twOrb_unit {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G)
    (horb : ∀ g₁ g₂ : G, g₁⁻¹ * γ * g₁ ∈ K → g₂⁻¹ * γ * g₂ ∈ K →
      ∃ t ∈ twCent (MonoidHom.id G) γ, ∃ k ∈ K, g₂ = t * g₁ * k)
    (hcpt : ∀ g : G, g⁻¹ * γ * g ∈ K →
      cptPart (twCent (MonoidHom.id G) γ) ≤ K.map (MulAut.conj g).toMonoidHom) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = if ∃ g : G, g⁻¹ * γ * g ∈ K then 1 else 0 := by
  classical
  set T := twCent (MonoidHom.id G) γ with hT
  have hTle : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hterm : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      ((((T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart T) : ℕ) : ℂ) *
        avg fun k : K => (K : Set G).indicator 1 ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
      = if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
    intro q
    have hconst : (fun k : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
        = fun _ => if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
      funext k
      have he : (Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)
          = (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k := by
        simp only [MonoidHom.id_apply]; group
      rw [he]
      by_cases hm : (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) k.2
        simp [Set.indicator_of_mem this, hm]
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∉ K := by
          intro h; apply hm
          have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)
          simpa [mul_assoc] using this
        simp [Set.indicator_of_notMem this, hm]
    rw [hconst, avg_const]
    split_ifs with hm
    · rw [(Subgroup.relIndex_eq_one).2 (le_inf hTle (hcpt _ hm))]; simp
    · simp
  rw [twOrb, finsum_congr hterm]
  split_ifs with hex
  · obtain ⟨g₀, hg₀⟩ := hex
    have hgood : ∀ g : G, g ∈ doubleCoset g₀ (T : Set G) (K : Set G) → g⁻¹ * γ * g ∈ K := by
      intro g hg
      obtain ⟨t, ht, k, hk, rfl⟩ := mem_doubleCoset.1 hg
      have htc : t * γ = γ * t := by simpa [hT, twCent] using ht
      have : (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * γ * g₀) * k := by
        have : t⁻¹ * γ * t = γ := by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
        calc (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * (t⁻¹ * γ * t) * g₀) * k := by group
          _ = _ := by rw [this]
      rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem hk) hg₀) hk
    rw [finsum_eq_single _ (DoubleCoset.mk T K g₀)]
    · rw [if_pos]
      obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul T K g₀
      apply hgood
      rw [he]; exact mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩
    · intro q hq
      rw [if_neg]
      intro hm
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := horb g₀ (Quotient.out q) hg₀ hm
      rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
      exact ⟨t⁻¹, T.inv_mem ht, k⁻¹, K.inv_mem hk, by rw [he]; group⟩
  · push_neg at hex
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro q; rw [if_neg (hex _)]

end GlobalTheory.BCT.OrbUnit

namespace GlobalTheory.BCT.OrbUnit

theorem orbUnit_ae : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ _ n _ S _ P hP
  filter_upwards [GlobalTheory.T.eventually_integral_lift_coprime_derivative E P hP.2.2.1] with w hw
  obtain ⟨P₀, hmap, hcop⟩ := hw
  obtain ⟨hσσ, hv⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
  intro γ hγ
  have hγ' : γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [hγ, hmap]
  refine ⟨?_, ?_, ?_⟩
  · exact twOrb_unit (KL n w) γ (GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w hσσ hv P₀ hcop γ hγ') (GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary E n w P₀ hcop γ hγ')
  · rw [← hγ]; exact GlobalTheory.T.localSign_full_charpoly_eq_one E n w hv γ.1
  · rintro Q₁ hQ ⟨g, hg⟩
    rw [← GlobalTheory.T.localSign_kernel_charFactor_conj_invariant E n w hv Q₁ γ g]
    refine GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction E n w hσσ hv P₀ hcop (g⁻¹ * γ * g) ?_ hg Q₁ (by rw [hmap]; exact hQ)
    rw [← hγ']
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val =
        ((g : GLw n w)⁻¹ : GLw n w).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [this, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.BCT.OrbUnit
end
end
