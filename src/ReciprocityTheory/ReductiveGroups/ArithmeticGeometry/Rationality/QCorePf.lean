module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreSt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreGlobPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPfH
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalLengthFraction

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH

variable {K₁ : Type} [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁))

instance isFractionRing_Rv : IsFractionRing (Rv K₁ w) K₁ :=
  (inferInstance : IsFractionRing (w.valuationSubringAtPrime K₁) K₁)

variable {U : Type} [AddCommGroup U] [Module K₁ U] [FiniteDimensional K₁ U]
  [Module (Rv K₁ w) U] [IsScalarTower (Rv K₁ w) K₁ U]

theorem local_len (hL : QuotLocalStatement) (P : Submodule K₁ U) (Mw : Submodule (Rv K₁ w) U)
    (hMw : Mw.FG) (hMspan : Submodule.span K₁ (Mw : Set U) = ⊤) {ρ : ℕ}
    (hρ : finrank K₁ (U ⧸ P) = ρ) (e : Fin ρ → U) (he : ∀ j, e j ∈ Mw)
    (c : Fin ρ → U →ₗ[K₁] K₁) (hcP : ∀ i, ∀ x ∈ P, c i x = 0) (s : Fin ρ → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (e j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv K₁ w) (Mw ⧸ ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
        Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype) = n ∧
      (n : ℝ) ≤ (ordAt w (Matrix.of fun i j => c i (e j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical
  set N : Submodule (Rv K₁ w) Mw := (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw).comap Mw.subtype
    with hN
  set T : Submodule (Rv K₁ w) Mw := ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
      Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype with hT

  have hspanP : ∀ x : U, x ∈ Submodule.span (Rv K₁ w) (P : Set U) → x ∈ P := fun x hx =>
    (Submodule.span_le (p := P.restrictScalars (Rv K₁ w))).mpr (fun y hy => hy) hx
  have hmemN : ∀ y : Mw, y ∈ N ↔ (y : U) ∈ P := by
    intro y
    constructor
    · intro hy
      exact hspanP _ (Submodule.mem_inf.mp (Submodule.mem_comap.mp hy)).1
    · intro hy
      exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨Submodule.subset_span hy, y.2⟩)

  let cQ : Fin ρ → (Mw ⧸ N) →ₗ[Rv K₁ w] K₁ := fun i =>
    N.liftQ (((c i).restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact hcP i _ ((hmemN y).mp hy))
  have hc' : ∀ i (q : Mw ⧸ N), cQ i q ≠ 0 → -β ≤ (ordAt w (cQ i q) : ℝ) + s i := by
    intro i q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact hint i y y.2 hq
  let e' : Fin ρ → Mw := fun j => ⟨e j, he j⟩
  let th : Fin ρ → Mw ⧸ N := fun j => N.mkQ (e' j)
  have hdet' : (Matrix.of fun i j => cQ i (th j)).det ≠ 0 := hdet

  let ι : (Mw ⧸ N) →ₗ[Rv K₁ w] (U ⧸ P) :=
    N.liftQ ((P.mkQ.restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero P (x := (y : U))).mpr ((hmemN y).mp hy))
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact (Submodule.Quotient.mk_eq_zero N (x := y)).mpr
      ((hmemN y).mpr ((Submodule.Quotient.mk_eq_zero P (x := (y : U))).mp hq))
  haveI : Module.Finite (Rv K₁ w) Mw := Module.Finite.iff_fg.mpr hMw
  haveI : NoZeroSMulDivisors (Rv K₁ w) (Mw ⧸ N) := by
    refine ⟨fun {r q} hrq => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply hι
    rw [map_zero]
    have h1 : r • ι q = 0 := by rw [← map_smul, hrq, map_zero]
    have hr' : (r • (1 : K₁)) ≠ 0 := by
      rw [Subring.smul_def, smul_eq_mul, mul_one]
      exact fun h => hr (Subtype.ext h)
    have h2 : (r • (1 : K₁)) • ι q = 0 := by rw [smul_one_smul]; exact h1
    exact (smul_eq_zero.mp h2).resolve_left hr'
  haveI : Module.Free (Rv K₁ w) (Mw ⧸ N) := Module.free_of_finite_type_torsion_free'

  have hthli : LinearIndependent (Rv K₁ w) th := by
    apply LinearIndependent.of_comp (LinearMap.pi fun i => cQ i)
    have hK : LinearIndependent K₁ (fun j => Matrix.transpose (Matrix.of fun i j => c i (e j)) j) :=
      Matrix.linearIndependent_cols_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    exact (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mpr hK
  have hle1 : ρ ≤ Module.finrank (Rv K₁ w) (Mw ⧸ N) := by
    simpa using hthli.fintype_card_le_finrank
  have hle2 : Module.finrank (Rv K₁ w) (Mw ⧸ N) ≤ ρ := by
    let b := Module.Free.chooseBasis (Rv K₁ w) (Mw ⧸ N)
    have hli : LinearIndependent (Rv K₁ w) (ι ∘ b) :=
      b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr hι)
    have hliK : LinearIndependent K₁ (ι ∘ b) :=
      (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mp hli
    rw [Module.finrank_eq_card_chooseBasisIndex, ← hρ]
    exact hliK.fintype_card_le_finrank
  have hb : Nonempty (Module.Basis (Fin ρ) (Rv K₁ w) (Mw ⧸ N)) :=
    ⟨Module.finBasisOfFinrankEq _ _ (le_antisymm hle2 hle1)⟩
  obtain ⟨n, hn, hle⟩ := exists_length_quotient_span_le hL w (Mw ⧸ N) ρ hb cQ s β th hc' hdet'

  have hmapE : (Submodule.span (Rv K₁ w) (Set.range e')).map Mw.subtype =
      Submodule.span (Rv K₁ w) (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hmapTh : (Submodule.span (Rv K₁ w) (Set.range e')).map N.mkQ =
      Submodule.span (Rv K₁ w) (Set.range th) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hNT : N ≤ T := Submodule.comap_mono le_sup_left
  have hspan : T.map N.mkQ = Submodule.span (Rv K₁ w) (Set.range th) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap]
      have hy' : (y : U) ∈ (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
          Submodule.span (Rv K₁ w) (Set.range e) := hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
      rw [← hmapE] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have hyab : y = ⟨a, ha.2⟩ + b' := Subtype.ext (by simpa using hab.symm)
      have h0 : N.mkQ ⟨a, ha.2⟩ = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (hmemN _).mpr (hspanP a ha.1)
      rw [hyab, map_add (f := _), h0, zero_add, ← hmapTh]
      exact Submodule.mem_map_of_mem hb'
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨e' j, Submodule.mem_comap.mpr
        (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)), rfl⟩
  let E : ((Mw ⧸ N) ⧸ Submodule.span (Rv K₁ w) (Set.range th)) ≃ₗ[Rv K₁ w] (Mw ⧸ T) :=
    (Submodule.quotEquivOfEq _ _ hspan.symm).trans (Submodule.quotientQuotientEquivQuotient N T hNT)
  exact ⟨n, (LinearEquiv.length_eq E).symm.trans hn, hle⟩

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalLengthAverage

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct

variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

lemma algebraMap_mem_Rv (w : HeightOneSpectrum (𝓞 K₁)) (a : 𝓞 K) :
    algebraMap K K₁ (algebraMap (𝓞 K) K a) ∈ Rv K₁ w := by
  have h1 : algebraMap K K₁ (algebraMap (𝓞 K) K a) =
      algebraMap (𝓞 K₁) K₁ (algebraMap (𝓞 K) (𝓞 K₁) a) := by
    first
      | rfl
      | simp [← IsScalarTower.algebraMap_apply]
  rw [h1]
  first
    | exact w.valuation_le_one _
    | exact w.valuation_le_one K₁ _
    | simp [Rv, HeightOneSpectrum.valuationSubringAtPrime, HeightOneSpectrum.valuation_le_one]

theorem lenW_bound (hL : QuotLocalStatement) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)))
    (w : HeightOneSpectrum (𝓞 K₁)) (s : Fin (finrank (𝓞 K) (QuotMW M W)) → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
      -β ≤ (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i) :
    ∃ n : ℕ, lenW w M W θ = n ∧
      (n : ℝ) ≤ (ordAt w (detCT c θ) : ℝ) + ∑ i, s i +
        (finrank (𝓞 K) (QuotMW M W) : ℝ) * β := by
  classical
  let inst : Module (Rv K₁ w) (K₁ ⊗[K] V) := Module.compHom _ (Rv K₁ w).subtype
  have hst : IsScalarTower (Rv K₁ w) K₁ (K₁ ⊗[K] V) :=
    ⟨fun r a x => mul_smul (r : K₁) a x⟩
  have hsmul : ∀ (r : Rv K₁ w) (x : K₁ ⊗[K] V), r • x = (r : K₁) • x := fun r x => rfl
  set Mw : Submodule (Rv K₁ w) (K₁ ⊗[K] V) := Submodule.span (Rv K₁ w)
    ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V)) with hMwdef
  have hgen : ∀ m ∈ M, (1 : K₁) ⊗ₜ[K] m ∈ Mw := fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  have hsc : ∀ (a : 𝓞 K) (m : V), (1 : K₁) ⊗ₜ[K] (a • m) =
      (⟨algebraMap K K₁ (algebraMap (𝓞 K) K a), algebraMap_mem_Rv w a⟩ : Rv K₁ w) •
        ((1 : K₁) ⊗ₜ[K] m) := by
    intro a m
    rw [hsmul, ← algebraMap_smul K a m, TensorProduct.tmul_smul,
      ← algebraMap_smul K₁ (algebraMap (𝓞 K) K a)]
  have hMwFG : Mw.FG := by
    obtain ⟨G, hG⟩ := hM
    refine ⟨G.image (fun a : V => (1 : K₁) ⊗ₜ[K] a), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact hgen g (hG ▸ Submodule.subset_span hg)
    · rw [hMwdef, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      have hm' : m ∈ Submodule.span (𝓞 K) (G : Set V) := by rw [hG]; exact hm
      clear hm
      show (1 : K₁) ⊗ₜ[K] m ∈ _
      induction hm' using Submodule.span_induction with
      | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
      | smul a b _ hb => rw [hsc]; exact Submodule.smul_mem _ _ hb
  have hMspan : Submodule.span K₁ (Mw : Set (K₁ ⊗[K] V)) = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hr : (Set.range fun m : M => (m : V)) = (M : Set V) := Subtype.range_coe
    have hv : v ∈ Submodule.span K (Set.range fun m : M => (m : V)) := by
      rw [hr, hspan]; trivial
    have h1 := tmul_mem_span (K₁ := K₁) (fun m : M => (m : V)) hv
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span (hgen m m.2)
  have hint' : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i := by
    intro i y hy hne
    have hball : w.valuation K₁ (c i y) ≤ WithZero.exp (-⌈-β - s i⌉) := by
      clear hne
      rw [hMwdef] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨m, hm, rfl⟩ := hz
        by_cases h0 : c i ((1 : K₁) ⊗ₜ[K] m) = 0
        · rw [h0, map_zero]; exact zero_le
        · have h1 := hint i m hm h0
          rw [val_eq_exp w h0, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le]
          linarith
      | zero => rw [map_zero, map_zero]; exact zero_le
      | add a b _ _ ha hb =>
        rw [map_add (f := _)]
        exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
      | smul r a _ ha =>
        show w.valuation K₁ (c i ((r : K₁) • a)) ≤ _
        rw [map_smul, smul_eq_mul, map_mul]
        exact le_trans (mul_le_of_le_one_left' ((mem_Rv_iff w _).mp r.2)) ha
    rw [val_eq_exp w hne, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le] at hball
    linarith
  have hcP : ∀ i, ∀ x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)),
      c i x = 0 := fun i x hx => (hc x).mpr hx i
  obtain ⟨n, hn1, hn2⟩ := @local_len K₁ _ _ w (K₁ ⊗[K] V) _ _ _ inst hst hL _ Mw hMwFG hMspan _ (quot_finrank M hM hspan W θ hθ)
    (fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) (fun j => hgen _ (θ j).2) (fun i => c i) hcP s β
    hint' (detCT_ne_zero M hM hspan W θ hθ c hc)
  exact ⟨n, hn1, hn2⟩

theorem average (la : HeightOneSpectrum (𝓞 K)) (L : ℕ∞) (D : K₁)
    (t : HeightOneSpectrum (𝓞 K₁) → ℝ) (ρ : ℕ) (B : ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 K₁), LiesOver w la → ∃ n : ℕ,
      (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) * L = n ∧
      (n : ℝ) ≤ (ordAt w D : ℝ) + t w + ρ * ((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * B)) :
    ∃ ℓ : ℕ, L = ℓ ∧ (ℓ : ℝ) ≤ (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) /
        (Module.finrank K K₁ : ℝ) + ρ * B := by
  classical
  let S := la.asIdeal.primesOver (𝓞 K₁)
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K₁)) :=
    FaithfulSMul.algebraMap_injective _ _
  let E : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la} ≃ S :=
    { toFun := fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨w.2.symm⟩⟩
      invFun := fun q => ⟨⟨q.1, q.2.1, fun h0 => la.ne_bot (by
          have h1 : la.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 K₁)) := q.2.2.over
          rw [h1, h0]
          exact Ideal.comap_bot_of_injective _ hinj)⟩, q.2.2.over.symm⟩
      left_inv := fun w => rfl
      right_inv := fun q => rfl }
  have hsumN : ∑ q : S, q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K K₁ := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K₁) K₁]
  have hn : 0 < Module.finrank K K₁ := Module.finrank_pos
  have hne : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff] at hS
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsumN
    omega
  obtain ⟨q0⟩ := hne
  obtain ⟨n0, hn0, -⟩ := h (E.symm q0).1 (E.symm q0).2
  have he0 : 0 < (E.symm q0).1.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_pos _ _
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ℕ, L = ℓ := by
    induction L using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top (by exact_mod_cast he0.ne')] at hn0
      exact ENat.top_ne_natCast n0 hn0
    | coe ℓ => exact ⟨ℓ, rfl⟩
  refine ⟨ℓ, rfl, ?_⟩
  have hq : ∀ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ ≤ (ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B) := by
    intro q
    obtain ⟨n, hn1, hn2⟩ := h (E.symm q).1 (E.symm q).2
    have h1 : ((q.1.ramificationIdx (𝓞 K) * ℓ : ℕ) : ℕ∞) = n := by push_cast; exact hn1
    have h2 : q.1.ramificationIdx (𝓞 K) * ℓ = n := by exact_mod_cast h1
    have h3 : (q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ = n := by exact_mod_cast h2
    rw [h3]
    exact hn2
  have hsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) ≤
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1 +
        ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) :=
    Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hq q) (Nat.cast_nonneg _)
  have hN : ∑ q : S, (q.1.ramificationIdx (𝓞 K) : ℝ) * (q.1.inertiaDeg (𝓞 K) : ℝ) =
      Module.finrank K K₁ := by exact_mod_cast hsumN
  have hfs : (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
      (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + t w.1)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) := by
    rw [← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype]
    rfl
  have hLsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((q.1.ramificationIdx (𝓞 K) : ℝ) * ℓ) =
      ℓ * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hRsum : ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) +
      t (E.symm q).1 + ρ * ((q.1.ramificationIdx (𝓞 K) : ℝ) * B)) =
      ∑ q : S, (q.1.inertiaDeg (𝓞 K) : ℝ) * ((ordAt (E.symm q).1 D : ℝ) + t (E.symm q).1) +
        ρ * B * Module.finrank K K₁ := by
    rw [← hN, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hLsum, hRsum] at hsum
  have hnpos : (0 : ℝ) < Module.finrank K K₁ := by exact_mod_cast hn
  rw [hfs, div_add' _ _ _ hnpos.ne', le_div_iff₀ hnpos]
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreLocalPf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain Module

theorem qcoreLocal : QCoreLocalStatement := by
  intro hLD hQL K K₁ V _ _ _ _ _ _ _ _ _ _ M hM hspan W θ hθ c hc be s hbe hs hint
  refine ⟨LocalQuotientRank.detCT_ne_zero (M := M) (hM := hM) (hspan := hspan) (W := W)
    (θ := θ) (hθ := hθ) (c := c) (hc := hc), ?_⟩
  intro la
  obtain ⟨ℓ, hℓ, hle⟩ := LocalLengthAverage.average (la := la)
    (L := lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))))
    (D := detCT c θ) (t := fun w => ∑ i, s i w)
    (ρ := Module.finrank (𝓞 K) (QuotMW M W)) (B := be la) (by
      intro w hw

      obtain ⟨n, hn, hnle⟩ := LocalLengthAverage.lenW_bound (hL := hQL) (M := M) (hM := hM)
        (hspan := hspan) (W := W) (θ := θ) (hθ := hθ) (c := c) (hc := hc) (w := w)
        (s := fun i => s i w) (β := (w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la)
        (hint := fun i m hm hne => hint la w hw i m hm hne)
      refine ⟨n, ?_, ?_⟩
      · rw [← hLD K K₁ V M hM hspan W θ la w hw]
        exact hn
      · simpa only using hnle)
  refine ⟨ℓ, hℓ, ?_⟩
  simpa only [nnFun] using hle

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCorePf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

theorem quotCore_of_local (hL : QuotLocalStatement) : QuotCoreStatement := by
  intro hLD K K₁ V _ _ _ _ _ _ _ _ _ _ M hfg hspan W θ hθ c hker be s hbe _ hs hint supN a Bθ Carch
    Bdeg hconj hshort harch hdeg
  obtain ⟨hdet, hloc⟩ :=
    qcoreLocal hLD hL K K₁ V M hfg hspan W θ hθ c hker be s hbe hs hint
  obtain ⟨hsupp, hglob⟩ :=
    qcoreGlobal_holds K K₁ V M _ θ c hdet s hs supN a Bθ Carch Bdeg hconj hshort harch hdeg
  refine ⟨Finsupp.ofSupportFinite _ hsupp, ?_, ?_⟩
  · intro la
    obtain ⟨ℓ, hℓ, hle⟩ := hloc la
    exact ⟨ℓ, hℓ, hle⟩
  · have hsum : ((Finsupp.ofSupportFinite _ hsupp).sum fun la v => v * logN la) =
        ∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) (detCT c θ) s la * logN la := by
      rw [finsum_eq_sum_of_support_subset (s := hsupp.toFinset)]
      · rfl
      · intro la hla
        rw [Set.Finite.coe_toFinset]
        exact Function.support_mul_subset_left _ _ hla
    rw [hsum]
    exact hglob

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end
