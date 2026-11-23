module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZeroStatement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.SemistableReduction.DetGramEqProdGramSchmidt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdPowOfZeros
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosure

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped TensorProduct

namespace GlobalTheory

theorem etale_of_finrank_le_card_algHom_algebraicClosure : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  intro E R _ _ _ _
  refine ⟨inferInstance, card_algHom_le_finrank E R (AlgebraicClosure E), fun hle => ?_⟩
  classical
  set Ω := AlgebraicClosure E
  set S := Ω ⊗[E] R
  set ι := S →ₐ[Ω] Ω
  have : Fintype ι := Fintype.ofFinite ι
  have hcard : Nat.card ι = Nat.card (R →ₐ[E] Ω) :=
    (Nat.card_congr (AlgHom.liftEquiv E Ω R Ω)).symm
  have hrank : Module.finrank Ω S = Module.finrank E R := Module.finrank_baseChange
  let φ : S →ₐ[Ω] (ι → Ω) := AlgHom.pi fun f => f
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro g hg
    have hs : ∀ i : ι, (fun j => if i = j then (1 : Ω) else 0) = Pi.single i 1 := fun i => by
      ext j; simp [Pi.single_apply, eq_comm]
    have hli := Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap Ω S Ω)
      (fun f => g (Pi.single f 1))
    have hc : ∀ f, g (Pi.single f 1) = 0 := by
      apply hli
      refine LinearMap.ext fun s => ?_
      have := LinearMap.congr_fun hg s
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      rw [LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ g]
      simp only [hs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ g]
    simp [hs, hc]
  have hinj : Function.Injective φ.toLinearMap := by
    have hle' : Module.finrank Ω S ≤ Module.finrank Ω (ι → Ω) := by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard, hrank]
      exact hle
    have hge : Module.finrank Ω (ι → Ω) ≤ Module.finrank Ω S := by
      have h := LinearMap.finrank_range_le φ.toLinearMap
      rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle' hge)).mpr hsurj
  have : IsReduced S := isReduced_of_injective φ.toRingHom hinj
  have : IsArtinianRing S := .of_finite Ω S
  have hE : Algebra.Etale Ω S := by
    have (I : MaximalSpectrum S) : Algebra.FormallyEtale Ω (S ⧸ I.asIdeal) := by
      let := Ideal.Quotient.field I.asIdeal
      exact Algebra.FormallyEtale.of_isSeparable Ω (S ⧸ I.asIdeal)
    exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars Ω).symm,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosureStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.etale_of_finrank_le_card_algHom : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  first | exact @GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | exact GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | (intros; apply GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtOfMemConeOfIsAlgClosed

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_pt_of_mem_cone_of_isAlgClosed : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosed K] (y : Fin S.N → K), y ≠ 0 → (∀ g ∈ S.imageIdeal, aeval y g = 0) → ∃ (x : S.Pt K) (c : K), c ≠ 0 ∧ S.coords x.1 = c • y := by
  intro F _ S hS hb K _ _ _ y hy hI
  classical
  by_contra hno
  push_neg at hno
  have hT : (S.baseChange K).IsVariety := hS.baseChange K
  have hbT : (S.baseChange K).BasePointFree := hb.baseChange K
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy
  change y i₀ ≠ 0 at hi₀
  let u : Fin S.N → Fin S.N → K := fun j => y i₀ • Pi.single j 1 - y j • Pi.single i₀ 1
  have hu : ∀ (j : Fin S.N) (c : Fin S.N → K), ∑ l, u j l * c l = y i₀ * c j - y j * c i₀ := fun j c => by
    simp [u, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, mul_assoc]

  have hcov : ∀ z : (S.baseChange K).Y, ∃ j, z ∈ nonzeroLocus ((S.baseChange K).comb (u j)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have := hT.smooth
    have : Smooth (S.baseChange K).str := SmoothOfRelativeDimension.smooth (S.baseChange K).D _
    have hZ : IsClosed (⋂ j, ((nonzeroLocus ((S.baseChange K).comb (u j)) : Set (S.baseChange K).Y)ᶜ)) :=
      isClosed_iInter fun j => (nonzeroLocus ((S.baseChange K).comb (u j))).isOpen.isClosed_compl
    obtain ⟨a, ha, haZ⟩ := GlobalTheory.ConeOnto.exists_rat_pt (S.baseChange K).str hZ.isLocallyClosed
      (x := z) (Set.mem_iInter.2 hz)
    let xa : (S.baseChange K).Pt K := ⟨a, ha.trans (Spec.map_id _).symm⟩
    have hbase : (S.baseChange K).baseHom a = RingHom.id K := LinSys.baseHom_ptOver xa
    have hv : ∀ j, y i₀ * (S.baseChange K).coords a j - y j * (S.baseChange K).coords a i₀ = 0 := fun j => by
      have h0 := Set.mem_iInter.1 (haZ (IsLocalRing.closedPoint K)) j
      have h1 : (S.baseChange K).val a ((S.baseChange K).comb (u j)) = 0 :=
        not_not.1 fun h => h0 (((S.baseChange K).val_ne_zero_iff a _).1 h)
      have h2 := ((S.baseChange K).val_comb a (u j)).symm.trans h1
      rw [hbase] at h2
      simp only [RingHom.id_apply] at h2
      exact (hu j ((S.baseChange K).coords a)).symm.trans h2
    have hc0 : (S.baseChange K).coords a i₀ ≠ 0 := fun h0 => hbT.coords_ne_zero a (funext fun j => by
      have := hv j
      rw [h0, mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀)
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange K a
    refine hno (LinSys.toBase xa) (c⁻¹ * ((S.baseChange K).coords a i₀ / y i₀))
      (mul_ne_zero (inv_ne_zero hc) (div_ne_zero hc0 hi₀)) (funext fun j => ?_)
    have ej := congrFun e j
    have hvj := hv j
    change S.coords (a ≫ S.bcFst K) j = _
    simp only [Pi.smul_apply, smul_eq_mul] at ej ⊢
    have e1 : S.coords (a ≫ S.bcFst K) j = c⁻¹ * (S.baseChange K).coords a j := by
      rw [ej, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have e2 : (S.baseChange K).coords a j = (S.baseChange K).coords a i₀ / y i₀ * y j := by
      field_simp
      linear_combination hvj
    rw [e1, e2]
    ring

  have hX : (X i₀ : MvPolynomial (Fin (S.baseChange K).N) K).IsHomogeneous 1 := isHomogeneous_X K i₀
  obtain ⟨m, A, hA, hrel⟩ := GlobalTheory.SecIntegral.exists_integral_relation K (S.baseChange K) hT S.N 1 u
    ((S.baseChange K).form hX) hcov
  let σ : Fin S.N → MvPolynomial (Fin S.N) K := fun i => ∑ j, C (u i j) * X j
  have hσ : ∀ i, (σ i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C (Fin S.N) (u i j)).mul (isHomogeneous_X K j)
  let G : MvPolynomial (Fin S.N) K := X i₀ ^ m + ∑ k : Fin m, bind₁ σ (A k) * X i₀ ^ (k : ℕ)
  have hG : G.IsHomogeneous m := by
    refine (isHomogeneous_X_pow i₀ m).add (IsHomogeneous.sum _ _ _ fun k _ => ?_)
    have h1 : (bind₁ σ (A k)).IsHomogeneous (1 * (1 * (m - k))) :=
      (hA k).eval₂ C σ (fun r => isHomogeneous_C _ r) hσ
    have h2 := h1.mul (isHomogeneous_X_pow i₀ (k : ℕ))
    have e : 1 * (1 * (m - (k : ℕ))) + k = m := by omega
    rwa [e] at h2

  haveI := HeightExists.isIntegral hT
  obtain ⟨Ω, _, _, xg, hxg, -⟩ := HeightExists.exists_generic hT
  have hmem : G ∈ (S.baseChange K).imageIdeal := by
    rw [imageIdeal_eq_coneIdeal_of_generic K Ω _ xg hxg 1 _ one_ne_zero (one_smul _ _).symm]
    refine (mem_coneIdeal_of_isHomogeneous (K := K) (N := S.N) _ hG).2 ?_
    have h := hrel Ω xg
    rw [LinSys.powVal_form, LinSys.baseHom_ptOver] at h
    erw [eval₂_X] at h
    let cg : Fin S.N → Ω := (S.baseChange K).coords xg.1
    have h' : cg i₀ ^ m + ∑ k : Fin m, aeval (fun i : Fin S.N => ∑ j : Fin S.N, algebraMap K Ω (u i j) * cg j) (A k) *
        cg i₀ ^ (k : ℕ) = 0 := h
    show aeval cg G = 0

    simp only [G, σ, map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_bind₁, aeval_C]
    exact h'

  rw [← HeightExists.map_imageIdeal hS K] at hmem
  have hker : S.imageIdeal.map (MvPolynomial.map (algebraMap F K)) ≤ RingHom.ker (eval y) :=
    Ideal.map_le_iff_le_comap.2 fun g hg => by
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map, ← aeval_def]
      exact hI g hg
  have h0 : eval y G = 0 := hker hmem
  have hA0 : ∀ k : Fin m, eval y (bind₁ σ (A k)) = 0 := fun k => by
    show aeval y (bind₁ σ (A k)) = 0
    rw [aeval_bind₁]
    have e : (fun i => aeval y (σ i)) = 0 := funext fun i => by

      simp only [σ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Pi.zero_apply]
      rw [hu i y]
      ring
    rw [e, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    exact (hA k).coeff_eq_zero (d := 0) (by simp; omega)
  have h3 : eval y G = y i₀ ^ m := by

    simp only [G, map_add (f := _), map_pow, map_sum, map_mul, eval_X, hA0, zero_mul, Finset.sum_const_zero, add_zero]
  exact pow_ne_zero m hi₀ (h3.symm.trans h0)

end GlobalTheory.ConeOnto
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowForm

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.HSChoice.EtaleSection

namespace GlobalTheory.HSShort.EtaleSection

theorem spec_zero_iff {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (δ : ℕ)
    (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (hf : IsChowForm T.imageIdeal T.D δ f)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) (ξ : Fin T.N → AlgebraicClosure E) :
    eval (fun p => ξ p.2) (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) = 0 ↔
      ∃ x ∈ T.geomPts E (T.linSection E s),
        ∑ j, ξ j * T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 j = 0 := by
  rw [eval_spec]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F _ _ δ _ f hf
  have hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 →
      ∑ j, u j * (c • y) j = 0 := fun u y c h => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
    rw [h, mul_zero]
  constructor
  · intro h0
    obtain ⟨y, hy, hc, h₁, h₂⟩ := hB _ _ _ h0
    obtain ⟨x₀, c, -, h⟩ := GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc
    obtain ⟨x, rfl⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀
    refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]
    · exact hs _ _ _ (h₁ i)
    · exact hs _ _ _ h₂
  · rintro ⟨x, hx, h⟩
    refine hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_)
      ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h
    have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg
    rwa [LinSys.baseHom_ptOver] at this

theorem simpleAt_of_noSquare : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  intro F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq
  classical
  obtain ⟨hfs, hmod, hrank⟩ := finite_finrank T hT E s hfin
  letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  haveI := hmod
  have hPfin : (T.geomPts E (T.linSection E s)).Finite := hfs.finite_subPts _
  have hcard := natCard_subPts _ _ hfs (AlgebraicClosure E)
  have hI := GlobalTheory.T.etale_of_finrank_le_card_algHom E Γ((T.linSection E s).subscheme, ⊤)
  set P := T.geomPts E (T.linSection E s) with hPdef
  set Ω := AlgebraicClosure E
  let yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω := fun x => T.coords (LinSys.toBase x : T.Pt Ω).1
  have hyv : ∀ x, yv x ≠ 0 := fun x => hT.alg.bpf.coords_ne_zero _
  let line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω) := fun x => Submodule.span Ω {yv x}
  have : Finite (line '' P) := (hPfin.image line).to_subtype
  let eR : (line '' P) ≃ Fin (Nat.card (line '' P)) := Finite.equivFin _
  have hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω)) :=
    fun q => (eR.symm q).2
  choose rep hrepP hrepl using hrep
  let y : Fin (Nat.card (line '' P)) → Fin T.N → Ω := fun q => yv (rep q)
  have hinj : ∀ q q', line (rep q) = line (rep q') → q = q' := by
    intro q q' h
    apply eR.symm.injective
    apply Subtype.ext
    rw [← hrepl, ← hrepl, h]
  have hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔
      ∃ q, ∑ j, ξ j * y q j = 0 := by
    intro ξ
    rw [spec_zero_iff T hT δ f hf E s ξ]
    constructor
    · rintro ⟨x, hx, h0⟩
      obtain ⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩ := ⟨_, eR.symm_apply_apply _⟩
      refine ⟨q0, ?_⟩
      have hl : line (rep q0) = line x := by rw [hrepl, hq0]
      have hm : y q0 ∈ line x := by
        rw [← hl]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]
      rw [h0, mul_zero]
    · rintro ⟨q, hq⟩
      exact ⟨rep q, hrepP q, hq⟩
  have hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q' := by
    intro q q' c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hyv _ (by simpa using h)
    apply hinj
    change Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}
    rw [show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨hmδ, c, hc, hfac⟩ := HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y
    (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero
  have hPf : Finite P := hPfin.to_subtype
  have hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P)) := fun q q' h =>
    hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])
  have hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ := hrank.trans hδ.symm
  have h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E) := hcard
  have h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ := by exact_mod_cast hfr
  have hPle : Nat.card P ≤ δ := by
    have h2 := hI.2.1
    omega
  have hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P := Nat.card_le_card_of_injective _ hrepinj
  rw [Nat.card_fin] at hmP
  have hPδ : Nat.card P = δ := by omega
  have hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P)) :=
    hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)
  refine ⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩
  · omega
  · rw [← Nat.card_coe_set_eq]
    exact hPδ
  · intro x hx x' hx' a ha h
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨q', hq'⟩ := hbij.2 ⟨x', hx'⟩
    obtain rfl : rep q = x := congrArg Subtype.val hq
    obtain rfl : rep q' = x' := congrArg Subtype.val hq'
    obtain ⟨b, hb, e⟩ := T.toLinSys.exists_coords_baseChange E (rep q).1
    obtain ⟨b', hb', e'⟩ := T.toLinSys.exists_coords_baseChange E (rep q').1
    have e₁ : b' • y q' = a • b • y q := e'.symm.trans (h.trans (congrArg (a • ·) e))
    rw [hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]
  · rw [hfac]
    congr 1
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
    refine finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩
      fun q _ => rfl
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩

end GlobalTheory.HSShort.EtaleSection
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowFormStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.linearSection_etale_of_squarefree_chowForm : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  first | exact @GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | exact GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | (intros; apply GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare <;> assumption)
end
end
