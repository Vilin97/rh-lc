module

import Mathlib.Tactic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.DimOne
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Inverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.MonoMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.NonAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivGr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinExt

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.finExt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
      (φ : A →+* B) (f : A →+* V), Function.Injective φ → φ.Finite → Function.Injective f →
      ∃ (y : B →+* V) (s : Finset K), y.comp φ = f ∧ ∀ b, (y b : K) ∈ Subfield.closure (Set.range (V.subtype.comp f) ∪ s) := by
  intro K _ _ V A B _ _ _ _ φ f hφ hfin hf
  classical
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A K := (V.subtype.comp f).toAlgebra
  letI : Algebra A V := f.toAlgebra
  haveI : Module.Finite A B := hfin
  have hfK : Function.Injective (V.subtype.comp f) := Subtype.val_injective.comp hf
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK
  haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  let y₀ : B →ₐ[A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hmem : ∀ b, y₀ b ∈ V := by
    intro b
    have h1 : IsIntegral A (y₀ b) := (Algebra.IsIntegral.isIntegral b).map y₀
    have h2 : IsIntegral V (y₀ b) := h1.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hz]
    exact z.2
  let y : B →+* V := y₀.toRingHom.codRestrict V hmem
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine ⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩
  · ext a
    exact y₀.commutes a
  · intro b
    show y₀ b ∈ _
    have hb : b ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Subfield.subset_closure
      right
      simp
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact add_mem hx hz
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem (Subfield.subset_closure ?_) hx
      left
      exact ⟨a, rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PsFinEv

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.psFin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsDomain B], (∀ a ∈ maximalIdeal O, algebraMap O B a = 0) →
      ∀ t ∈ maximalIdeal B, t ≠ 0 → ∀ n : ℕ, maximalIdeal B ^ n ≤ Ideal.span {t} →
      ∃ φ : PowerSeries (ResidueField O) →+* B, Function.Injective φ ∧ φ.Finite ∧ φ PowerSeries.X = t ∧
        ∀ a : O, φ (PowerSeries.C (residue O a)) = algebraMap O B a := by
  intro O _ _ B _ _ _ _ h0 t ht ht0 n hn
  classical
  let ι : ResidueField O →+* B := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0
  letI : UniformSpace (ResidueField O) := ⊥
  letI : WithIdeal B := ⟨maximalIdeal B⟩
  have hadic : IsAdic (maximalIdeal B) := rfl
  have hc : CompleteSpace B ∧ T2Space B := hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))
  haveI := hc.1
  haveI := hc.2
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hte : PowerSeries.HasEval t := by
    show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with m hm
    exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)
  let φ := PowerSeries.eval₂Hom hcont hte
  have hφX : φ PowerSeries.X = t := by simp [φ, PowerSeries.coe_eval₂Hom]
  have hφC : ∀ r, φ (PowerSeries.C r) = ι r := by
    intro r
    simp [φ, PowerSeries.coe_eval₂Hom]
  refine ⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have h1 := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    rw [map_mul, map_pow, hφX, hf] at h1
    exact mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1
  · letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra
    haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B)
        (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
        RingHom.algebraMap_toAlgebra, hφX]
    show Module.Finite _ _
    refine UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_
    · rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    · intro x
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
      exact ⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩
    · rw [hmap]
      exact hn
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.AmbPt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ambPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B], ¬ Module.Finite c.O B →
      ∃ (𝔞 : Amb l) (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (s : Finset 𝔞.K)
        (y : B →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ y.comp (algebraMap c.O B) = 𝔞.a c ∧ (∀ b ∈ maximalIdeal B, y b ∈ maximalIdeal 𝔞.V) ∧
        (∃ b ∈ maximalIdeal B, y b ≠ 0) ∧ (∀ a ∈ maximalIdeal c.O, 𝔞.a c a = 0) ∧
        ∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) := by
  intro l _ c B _ _ _ hB
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨P, t, n, hP, hmP, ht, htP, hn⟩ := Po.dimOne c.O B hB
  haveI : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsCO c.O (B ⧸ P) := co_quot c.O B _ (Ideal.Quotient.mkₐ c.O P) (Ideal.Quotient.mkₐ_surjective c.O P)
  have hq : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal B).map (Ideal.Quotient.mk P) = maximalIdeal (B ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hq
  have h0 : ∀ a ∈ maximalIdeal c.O, algebraMap c.O (B ⧸ P) a = 0 := fun a ha =>
    (Ideal.Quotient.eq_zero_iff_mem (a := algebraMap c.O B a)).2 (hmP (Ideal.mem_map_of_mem _ ha))
  have hn' : maximalIdeal (B ⧸ P) ^ n ≤ Ideal.span {Ideal.Quotient.mk P t} := by
    rw [← hm, ← Ideal.map_pow]
    refine (Ideal.map_mono hn).trans ?_
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨φ, hφi, hφf, hφX, hφC⟩ := Po.psFin c.O (B ⧸ P) h0 (Ideal.Quotient.mk P t)
    (hm ▸ Ideal.mem_map_of_mem _ ht) (fun h => htP (Ideal.Quotient.eq_zero_iff_mem.1 h)) n hn'
  obtain ⟨hfin, hch⟩ := Po.fin_res c
  haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField c.O))) (PowerSeries (ResidueField c.O)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  haveI : Finite (ResidueField (PowerSeries (ResidueField c.O))) :=
    Finite.of_equiv _ (PowerSeries.residueFieldOfPowerSeries (k := ResidueField c.O)).symm.toEquiv
  haveI : CharP (PowerSeries (ResidueField c.O)) l :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ResidueField c.O)) l
  obtain ⟨𝔞, f, hK, hf, hfa⟩ := ambL c (PowerSeries (ResidueField c.O)) (PowerSeries.C.comp (residue c.O))
  obtain ⟨y, s, hy, hs⟩ := Po.finExt 𝔞.K 𝔞.V _ _ φ f hφi hφf hf.inj
  have hyφ : ∀ x, y (φ x) = f x := fun x => RingHom.congr_fun hy x
  have hya : ∀ a, y (algebraMap c.O (B ⧸ P) a) = 𝔞.a c a := fun a => by
    rw [← hφC, hyφ, ← hfa]
    rfl
  have hX : f PowerSeries.X ∈ maximalIdeal 𝔞.V := by
    haveI := hf.loc
    refine map_nonunit f _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  refine ⟨𝔞, _, inferInstance, inferInstance, inferInstance, f, s, y.comp (Ideal.Quotient.mk P), hK, hf,
    RingHom.ext hya, fun b hb => ?_, ⟨t, ht, ?_⟩, fun a ha => ?_, fun b => hs _⟩
  · have hb' : Ideal.Quotient.mk P b ∈ maximalIdeal (B ⧸ P) := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hn' (Ideal.pow_mem_pow hb' n))
    refine (maximalIdeal.isMaximal 𝔞.V).isPrime.mem_of_pow_mem n ?_
    rw [RingHom.comp_apply, ← map_pow, ← hu, map_mul, ← hφX, hyφ]
    exact Ideal.mul_mem_left _ _ hX
  · rw [RingHom.comp_apply, ← hφX, hyφ]
    exact fun h => PowerSeries.X_ne_zero (hf.inj (h.trans (map_zero f).symm))
  · rw [← hya, h0 a ha, map_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtOver

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_map {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R') {I : Ideal R} {I' : Ideal R'}
    (h : ∀ x ∈ I, f x ∈ I') {F : Γ → R} (hF : AdicCont I F) : AdicCont I' fun g => f (F g) := fun N => by
  have hle : I ^ N ≤ (I' ^ N).comap f := le_trans (Ideal.pow_right_mono h N) (Ideal.le_comap_pow _ N)
  exact (hF N).comp (Ideal.quotientMap _ f hle)

theorem UpperTheory.V.Ws.ptOver :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ¬ D.Fin0 → ∃ (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V), CharP 𝔞.K l ∧ VPt D 𝔞 r ∧ ∃ x ∈ mono r 0, ∀ n : ℕ, 0 < n → x ^ l ^ n ≠ x := by
  intro hC Ω _ _ _ l _ c D hD hF
  obtain ⟨U, _, _, _, ρ, W, hpt, hz, hform, hnf⟩ := Po.univGr hC D hD hF
  haveI : IsCO c.O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O _ U W hz
  obtain ⟨hmax, u, hu, hspan⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials c.O _ U W hz
  obtain ⟨𝔞, A, _, _, _, f, s, y, hch, hf, hy, hloc, ⟨b, hb, hb0⟩, hO, hcl⟩ := Po.ambPt c (W.gr 0) hnf
  obtain ⟨A', _, _, _, f', Ξ, hf', hΞ, hext⟩ :=
    Po.ptA 𝔞 A f hf s c.O _ U W hz y (fun b hb => hloc b ((hmax b).2 hb)) hcl
  let Y : U →+* 𝔞.V := f'.comp Ξ
  have hya : ∀ a, y (algebraMap c.O (W.gr 0) a) = 𝔞.a c a := fun a => RingHom.congr_fun hy a
  have hYa : ∀ a, Y (algebraMap c.O U a) = 𝔞.a c a := fun a => by
    have e : ((algebraMap c.O (W.gr 0) a : W.A) : U) = algebraMap c.O U a := by
      simp
    rw [← hya, ← hext, e]
    rfl
  have hYm : ∀ x ∈ maximalIdeal U, Y x ∈ maximalIdeal 𝔞.V := fun x hx => by
    haveI := hf'.loc
    exact map_nonunit f' _ (hΞ x hx)
  refine ⟨𝔞, mapRep Y ρ.hom, hch, ⟨⟨A', inferInstance, inferInstance, inferInstance, f', ⟨mapRep Ξ ρ.hom, fun _ => 1⟩, hf',
    fun i j => cont_map Ξ hΞ (ρ.cont i j), PD.ext rfl (funext fun _ => Matrix.map_one _ (map_zero _) (map_one _))⟩,
    U, inferInstance, inferInstance, inferInstance, ρ, Y, hpt, RingHom.ext hYa, hYm, rfl⟩, ?_⟩
  have hex : ∃ v ∈ u, y v ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hb0 (show b ∈ RingHom.ker y from (?_ : maximalIdeal (W.gr 0) ≤ RingHom.ker y) hb)
    rw [hspan]
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) (Ideal.span_le.2 fun v hv => hn v hv)
    show y _ = 0
    rw [hya, hO a ha]
  obtain ⟨v, hv, hv0⟩ := hex
  obtain ⟨n, -, hn, hvn⟩ := hu v hv
  haveI := (Po.fin_res c).1
  haveI : CharP 𝔞.V l := haveI := hch; 𝔞.V.subtype.charP Subtype.val_injective l
  have hvm : v ∈ maximalIdeal (W.gr 0) := hspan ▸ Ideal.mem_sup_right (Ideal.subset_span hv)
  refine Po.nonAlg l c.O _ U ρ.hom 𝔞.V Y (fun a ha => by rw [hYa, hO a ha]) ((v : W.A) : U) ?_ (hYm _ ((hmax v).1 hvm)) ?_
  · rw [hvn]
    exact Po.zMono c.O _ U ρ.hom W (fun g a b => D.r0 g a b)
      (fun g a b h => Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) h) hform n hn
  · show f' (Ξ _) ≠ 0
    rwa [hext]
end
end
