module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPow
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairing

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem cartier_primePow_pairing (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r :=
  convPow_primePow_apply_pow p R h G n r χ a

end GlobalTheory.Katz
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairingStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.cartierDual_primePow_conv_pairing : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n), (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  first | exact @GlobalTheory.Katz.cartier_primePow_pairing | exact GlobalTheory.Katz.cartier_primePow_pairing | (intros; apply GlobalTheory.Katz.cartier_primePow_pairing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangent

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.FrobKerDim

theorem finrank_quot_frobKerIdeal_le : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H]
    [Module.Finite K H], 0 < q →
    Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  intro q K H _ _ _ _ hq
  classical
  set J := frobKerIdeal q K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨q, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l

    simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1

    simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ q = 0 := fun i => hpowQ _ (hy i)

  let mon : (Fin d → Fin q) → H ⧸ J := fun e => ∏ i, y i ^ (e i : ℕ)
  have htop : Submodule.span K (Set.range mon) = ⊤ := by
    have hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon) := by
      intro P
      induction P using MvPolynomial.induction_on' with
      | monomial u a =>
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
          ← Algebra.smul_def]
        refine Submodule.smul_mem _ _ ?_
        by_cases h : ∀ i, u i < q
        · exact Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩
        · push_neg at h
          obtain ⟨i, hi⟩ := h
          have h0 : y i ^ u i = 0 := pow_eq_zero_of_le hi (hyq i)
          rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]
          exact Submodule.zero_mem _
      | add P Q hP hQ => rw [map_add (f := _)]; exact Submodule.add_mem _ hP hQ
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨P, rfl⟩ := hsurj z
    exact hall P
  have h1 := finrank_range_le_card (R := K) (b := mon)
  rw [Set.finrank, htop, finrank_top] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end GlobalTheory.FrobKerDim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangentStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H] [Module.Finite K H], 0 < q → Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | exact GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | (intros; apply GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLe

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

open Coalgebra Bialgebra WithConv

namespace GlobalTheory.SpanPow

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

def annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) : Ideal (G.dual.A r) where
  carrier := {χ | ∀ a : G.A r, (show CartierDual K (G.A r) from χ) (a ^ p ^ r) = 0}
  add_mem' {χ ψ} hχ hψ a := by
    have e1 := hχ a
    have e2 := hψ a
    change (χ.ofConv + ψ.ofConv) (a ^ p ^ r) = 0
    rw [LinearMap.add_apply]
    change χ.ofConv (a ^ p ^ r) = 0 at e1
    change ψ.ofConv (a ^ p ^ r) = 0 at e2
    rw [e1, e2, add_zero]
  zero_mem' a := rfl
  smul_mem' c χ hχ a := by
    change (show CartierDual K (G.A r) from c * χ) (a ^ p ^ r) = 0
    rw [CartierDual.mul_apply, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rcases subsingleton_or_nontrivial (G.A r ⊗[K] G.A r) with hs | hn
    · rw [Subsingleton.elim ((comul (R := K) a) ^ p ^ r) 0, map_zero]
    · haveI : CharP (G.A r ⊗[K] G.A r) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
        rw [← map_natCast (algebraMap K (G.A r ⊗[K] G.A r)), h, map_zero])
      haveI : ExpChar (G.A r ⊗[K] G.A r) p := ExpChar.prime (Fact.out : p.Prime)
      have rep := Coalgebra.Repr.arbitrary K a

      rw [← rep.eq, sum_pow_char_pow, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_pow, CartierDual.pair_tmul_tmul]
      have e := hχ (rep.right i)
      change χ.ofConv _ = 0 at e
      rw [e, mul_zero]

theorem frobKerIdeal_le_annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) :
    frobKerIdeal (p ^ r) K (G.dual.A r) ≤ annPowIdeal h G r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨χ, hχ, rfl⟩ a
  have h1 := GlobalTheory.T.cartierDual_primePow_conv_pairing p K h G r r χ a
  have hχ' : χ.ofConv 1 = 0 := hχ
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = 0
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = χ.ofConv (mulBy K (G.A r) (p ^ r) a) ^ p ^ r at h1
  rw [h1, G.mulBy_pow_self r a, Algebra.algebraMap_eq_smul_one, map_smul, hχ', smul_zero,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end GlobalTheory.SpanPow

open GlobalTheory.SpanPow in
theorem GlobalTheory.finrank_span_pow_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  intro p _ K _ h G r
  set S := Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r) with hS
  let D := G.dual.A r
  let ev : D →ₗ[K] Module.Dual K S := S.subtype.dualMap ∘ₗ (CartierDual.toDual K (G.A r)).toLinearMap
  have hev : Function.Surjective ev :=
    (LinearMap.dualMap_surjective_of_injective S.injective_subtype).comp
      (CartierDual.toDual K (G.A r)).surjective
  let J := frobKerIdeal (p ^ r) K D
  have hle : J.restrictScalars K ≤ LinearMap.ker ev := by
    intro χ hχ
    have hT := frobKerIdeal_le_annPowIdeal h G r hχ
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun s => ?_
    obtain ⟨s, hs⟩ := s
    change χ.ofConv s = 0
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hT a
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  let φ : (D ⧸ J) →ₗ[K] Module.Dual K S :=
    (J.restrictScalars K).liftQ ev hle ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hev y
    refine ⟨Ideal.Quotient.mk J x, ?_⟩
    rfl
  have h1 : Module.finrank K S ≤ Module.finrank K (D ⧸ J) := by
    have := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.2 hφ, finrank_top, Subspace.dual_finrank_eq] at this
    exact this
  have h2 := GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent (p ^ r) K D (pow_pos (Fact.out : p.Prime).pos r)
  have hfin := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G.dual).1
  have h3 : Module.finrank K (Cot K D) ≤ Module.finrank K G.dual.omega := by
    have := LinearMap.finrank_range_le (G.dual.omegaLevel r)
    rwa [LinearMap.range_eq_top.2 (G.dual.omegaLevel_surjective r), finrank_top] at this
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos r) h3))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLeStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.finrank_span_pow_pDivGroup_level_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  first | exact @GlobalTheory.finrank_span_pow_le | exact GlobalTheory.finrank_span_pow_le | (intros; apply GlobalTheory.finrank_span_pow_le <;> assumption)
end
end
