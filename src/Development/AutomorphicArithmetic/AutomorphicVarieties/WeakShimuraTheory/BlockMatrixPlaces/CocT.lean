module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
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
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Compat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GammaOneGammaZeroHomogeneousCocyclesFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwIneq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlaceSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.SelToZc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.IsPrecompleteFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.DivStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CardP

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlusCard

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.plusCard :
    LocalFiniteness → LocalEulerChar → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) M), 0 < r → IsPlaceOver B v → ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ContAction ρ →
          ∀ P : Submodule (ZMod (l ^ r)) M, (∀ h, ∀ x ∈ P, ρ h x ∈ P) → (∃ s, Function.Bijective fun x => ρ s x - x) →
          ∃ L : Submodule (ZMod (l ^ r)) (H1 ρ), Nat.card P ≤ Nat.card L ∧ ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ L → ∃ y, ∀ h, z.1 h - (ρ h y - y) ∈ P := by
  intro hFin hEul Ω _ _ _ l _ r M _ _ _ _ _ B v ρ hr hB hl hc P hP hs
  let ρP : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) P :=
    { toFun := fun h => (ρ h).restrict (fun x hx => hP h x hx)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hρP : ∀ h (x : P), ((ρP h x : P) : M) = ρ h x := fun _ _ => rfl
  have hcP : ContAction ρP := by
    have h1 : Continuous fun p : Dec (F := ℚ) B × P => ρ p.1 (p.2 : M) :=
      hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact continuous_induced_rng.2 h1
  obtain ⟨hH0, hH1, hH2, -⟩ := hFin ℚ Ω l r P B ρP v hr hB hcP
  have hE := (hEul ℚ Ω l r P B ρP v hr hB hcP).1 hl
  have hdeg : 0 < locDeg v := by
    unfold locDeg
    exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : Nat.card P ≤ Nat.card (H1 ρP) := by
    rw [hE]
    have a0 : 0 < Nat.card (H0 ρP) := Nat.card_pos
    have a2 : 0 < Nat.card (H2 ρP) := Nat.card_pos
    calc Nat.card P ≤ Nat.card P ^ locDeg v := Nat.le_self_pow hdeg.ne' _
      _ ≤ Nat.card (H0 ρP) * Nat.card (H2 ρP) * Nat.card P ^ locDeg v :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos a0 a2)
  have hu : Continuous (P.subtype : P → M) := continuous_subtype_val
  have heq : ∀ (g : Dec (F := ℚ) B) (m : P), P.subtype (ρP g m) = ρ g (P.subtype m) := fun _ _ => rfl
  let φ := mapH1 ρP ρ P.subtype hu heq
  obtain ⟨s, hsb⟩ := hs
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hw' : (φ (Submodule.Quotient.mk w)) = 0 := hw
    simp only [φ, mapH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at hw'
    rw [mem_coboundaries1] at hw'
    obtain ⟨m, hm⟩ := hw'
    have hm' : ∀ g, ((w.1 g : P) : M) = ρ g m - m := fun g => hm g
    have hmP : m ∈ P := by
      obtain ⟨q, hq⟩ : ∃ q : P, ρP s q - q = w.1 s := by
        have hinjP : Function.Injective fun q : P => ρP s q - q := by
          intro a b hab
          apply Subtype.ext
          apply hsb.1
          have := congrArg Subtype.val hab
          simpa [hρP] using this
        exact (Finite.injective_iff_surjective.1 hinjP) (w.1 s)
      have h1 : ρ s (q : M) - q = ρ s m - m := by
        have := congrArg Subtype.val hq
        simp only [AddSubgroupClass.coe_sub, hρP] at this
        rw [this, hm' s]
      have := hsb.1 h1
      rw [← this]
      exact q.2
    rw [Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨⟨m, hmP⟩, fun g => ?_⟩
    apply Subtype.ext
    rw [hm' g]
    rfl
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · calc Nat.card P ≤ Nat.card (H1 ρP) := hle
      _ = Nat.card (LinearMap.range φ) := Nat.card_congr (LinearEquiv.ofInjective φ hinj).toEquiv
  · intro z hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    simp only [φ, mapH1, Submodule.mapQ_apply] at hw
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨-y, fun h => ?_⟩
    have h1 := hy h
    have h2 : ((cocycles1MapOfEquivariant ρP ρ P.subtype hu heq w : Z1 ρ) : _ → M) h = (w.1 h : M) := rfl
    simp only [Submodule.coe_sub, Pi.sub_apply, h2] at h1
    have h3 : z.1 h - (ρ h (-y) - -y) = (w.1 h : M) := by
      rw [map_neg]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    rw [h3]
    exact (w.1 h).2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwCount

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.gwCount :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → (∀ m, ρ c m = -m) → (Function.Bijective fun m => ρ s m - m) →
          ∀ P : Submodule R M, (∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P, ρ h x ∈ P) → Nat.card P ≤ Nat.card (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := by
  classical
  intro hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs
  have hfin := zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)
  haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin
  obtain ⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩ := placeSet (l := l) S B hP.prime hP.mem hP.ovl
  subst hB
  have hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hcl : IsClosed (ρ.ker : Set (G ℚ Ω)) := by
    have e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1
  have hN := hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK
  let ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  let σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by
      rw [show ρ g = 1 from hN hg]; rfl
  have hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m := fun _ _ => rfl
  have hcont : ContAction σ := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous
  have hloc : ∀ v, ContAction (σ.comp (locFam S' Av v)) := fun v =>
    Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont
      (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)
  let P' : Submodule (ZMod (l ^ (r + 1))) M := AddSubgroup.toZModSubmodule _ P.toAddSubgroup
  obtain ⟨L0, hL0, hL0'⟩ := plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0))
    r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩
  let L : LocCond σ (locFam S' Av) := Function.update
    (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0
  have hLv0 : L v0 = L0 := Function.update_self ..
  have hLv : ∀ v, v ≠ v0 →
      L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) :=
    fun v hv => Function.update_of_ne hv ..
  have h1 := gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L
    fun v hv => by
      obtain ⟨φ, -, h1, h2⟩ := GC.decZhat ℚ Ω v.1 (Av v) (hAv v)
      rw [hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]
  have h2 : Function.Bijective fun m : M => m + m := by
    refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)
    intro m hm
    have hm2 : 2 • m = 0 := by rw [two_smul]; exact hm
    have hco : Nat.Coprime 2 (l ^ r) :=
      ((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))
    rw [hco.gcd_eq_one, Nat.dvd_one] at this
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  obtain ⟨f, hf⟩ := selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K
    (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le)
    (fun z hz => hL0' z (hLv0 ▸ hz))
  rw [hLv0] at h1
  exact hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PrimEx

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CocT

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cocT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (ρ : Representation A (G ℚ Ω) T) (P : Submodule A T) (K : Subgroup (G ℚ Ω)),
          IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → Lat ρ (Dec (F := ℚ) B) P → (Function.Bijective fun x => ρ s x - x) → (∀ x, ρ c x = -x) → K ≤ ρ.ker → (∀ A', Raw.Away S A' → Ine (F := ℚ) A' ≤ K) →
          ∃ (z : G ℚ Ω → T) (y : T), IsZT ρ c (neSet l K) (Dec (F := ℚ) B) P z y ∧ z ≠ 0 := by
  intro hC Ω _ _ _ l _ S c s B hP A _ _ _ _ T _ _ _ _ ρ P K hA hl hL hs hc hK hU
  have hcard := cardP A T P hL.sat hL.ne
  have hfin : ∀ n, Finite (T ⧸ lev A T n) := fun n => (hcard n).1
  have htor : ∀ n, ∀ m : T ⧸ lev A T n, (l ^ n) • m = 0 := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul A, Nat.cast_pow]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top
  have hlc : ∀ n, ∀ m : T ⧸ lev A T n, IsLocallyConstant fun g => modRep ρ n g m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    exact hL.cont n x
  have hker : ∀ n, K ≤ (modRep ρ n).ker := by
    intro n g hg
    have h1 : ρ g = 1 := hK hg
    refine LinearMap.ext fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, h1]
    rfl
  have hneg : ∀ n, ∀ m : T ⧸ lev A T n, modRep ρ n c m = -m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, hc, map_neg]
  have hbij : ∀ n, Function.Bijective fun m : T ⧸ lev A T n => modRep ρ n s m - m := by
    intro n
    haveI := hfin n
    refine Finite.surjective_iff_bijective.1 fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    obtain ⟨y, rfl⟩ := hs.2 x
    exact ⟨(lev A T n).mkQ y, by simp only [modRep_mk, map_sub]⟩
  have hstab : ∀ n, ∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P.map (lev A T n).mkQ, modRep ρ n h x ∈ P.map (lev A T n).mkQ := by
    rintro n h hh _ ⟨x, hx, rfl⟩
    exact ⟨ρ h x, hL.stab h hh x hx, rfl⟩
  have hZ : ∀ n, (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n).Finite := fun n => by
    haveI := hfin n
    exact zcFin hC.gf S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU _
  have hge : ∀ n, n ≤ Nat.card (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n) := fun n => by
    haveI := hfin n
    exact (hcard n).2.trans
      (gwCount hC S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU (hneg n) (hbij n) _ (hstab n))
  obtain ⟨z, y, h1, h2, h3, h4⟩ := compat A T _ ρ c _ _ P hfin hZ (primEx A T _ ρ c _ _ P hL hZ hge)
  exact limit A T _ ρ c _ _ P hA z y h1 h2 h3 h4
end
end
