module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.H2SubsingletonTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GammaGen

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧ κ.ker = (cycU l U).subgroupOf U ∧
        κ γ = Multiplicative.ofAdd 1 ∧ U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧ ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUg hu
    simp only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h
    exact h.2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := by
    intro h
    apply hUk
    intro u hu
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    exact hχc.comp continuous_subtype_val
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := by
    intro x
    have h1 : κ x = e (ψ x) := rfl
    rw [h1, map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hSc : IsClosed S := hVc.preimage continuous_subtype_val
    have hIc : IsClosed (κ '' S) := (hSc.isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := Multiplicative.ofAdd ⁻¹' (κ '' S)
    have hTc : IsClosed T := hIc.preimage continuous_ofAdd
    have hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T := by
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    have hT : T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← PadicInt.denseRange_intCast.closure_range]
      exact closure_minimal hTz hTc
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hks' : κ s = κ ⟨u, hu⟩ := hks
    have hq : κ (⟨u, hu⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hks', mul_inv_cancel]
    have hq' := (hkκ _).mp hq
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V := by
      apply hsub
      apply Subgroup.mem_sup_right
      simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩
    have hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) := by
      simp
    rw [hu']
    exact V.mul_mem hmem hs
  · intro hfin
    have hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l) := ⟨γ.1, γ.2, rfl⟩
    have h1 := (hkκ γ).mpr (htor _ hm hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ControlGamma

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem exists_val (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ W : ValuationSubring Ω, W.valuation (p : Ω) < 1 := by
  have hne : (Ideal.span {(p : (⊥ : Subring Ω))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, (ValuationSubring.mem_nonunits_iff W).1 (hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem inj_cyc (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ)
    [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ) (hn : n ≠ 0) (hψo : IsOpen (ψ.ker : Set (G k Ω)))
    (V : Subgroup (G k Ω)) (hV : IsClosed (V : Set (G k Ω))) (hg : V ≤ gamU l ⊤) (hψ : V ≤ ψ.ker)
    (hχ : ¬ V ≤ (cycZ k Ω l).ker) :
    Function.Injective (resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l V)) := by
  obtain ⟨κ, γ, -, -, hk, -, hcl, hfin⟩ := gammaGen k Ω l V hV hg hχ
  haveI : ((cycU l V).subgroupOf V).Normal := hk ▸ inferInstance
  refine (kerResCyc O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (cycU l V) V (cycU_le l V) γ.1 γ.2 hcl).2 ?_
  intro m _
  have hall : ∀ m' : QO l O, m' ∈ H0U (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU l V) := by
    intro m' u
    have h1 : ψ u.1 = 1 := hψ u.2.1
    have h2 : cycZ k Ω l u.1 = 1 := u.2.2
    have h3 : (ψ * chiO k Ω l O ^ n) u.1 = 1 := by
      simp [chiO, h1, h2]
    show (((ψ * chiO k Ω l O ^ n) u.1 : Oˣ) : O) • m' = m'
    rw [h3, Units.val_one, one_smul]
  have ha : (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) - 1 ≠ 0 := by
    intro h0
    have h1 : ψ γ.1 = 1 := hψ γ.2
    have h2 : (ψ * chiO k Ω l O ^ n) γ.1 = 1 := Units.ext (sub_eq_zero.1 h0)
    have h3 : Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l γ.1 ^ n) = 1 := by
      rw [map_zpow]
      simpa [chiO, h1] using h2
    have h4 : cycZ k Ω l γ.1 ^ n = 1 :=
      Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) (dvrFacts l O).1 (h3.trans (map_one _).symm)
    exact hfin (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn, h4⟩)
  obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 _ ha m
  refine ⟨m', hall m', ?_⟩
  show (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) • m' - m' = m
  rw [← hm', sub_smul, one_smul]

private theorem mem_selEig_one {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [IsTopologicalGroup G] [DiscreteTopology M]
    (ρ : Representation R G M) (U' : Subgroup G) [U'.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (U : Subgroup G) (x : LocSel ρ U' 𝒟) : x ∈ selEig ρ U' h𝒟 U 1 ↔ x.1 ∈ invariantsUnderSubgroupH1 ρ U U' := by
  unfold selEig
  rw [eig_one]
  exact ⟨fun h g => congrArg Subtype.val (h g), fun h g => Subtype.ext (h g)⟩

theorem UpperTheory.V.Base.controlGamma :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal], IsOpen (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l hl O _ _ _ _ _ U _ hU hg ψ n hψ hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hψo : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hψ hU
  have hUc : IsClosed (U : Set (G k Ω)) := U.isClosed_of_isOpen hU
  have hnt : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ¬ U ⊓ Dec (F := k) A ≤ (cycZ k Ω l).ker := by
    intro A hA h
    obtain ⟨g, hgm, hf⟩ := decInf k Ω l U hU A hA
    exact hf (by rw [MonoidHom.mem_ker.1 (h hgm)]; exact IsOfFinOrder.one)
  have hχ : ¬ U ≤ (cycZ k Ω l).ker := by
    obtain ⟨A, hA⟩ := exists_val Ω l hl.out
    exact fun h => hnt A hA (inf_le_left.trans h)
  refine ⟨fun a b hab => Subtype.ext
    (inj_cyc k Ω l O ψ n hn hψo U hUc hg hψ hχ (congrArg Subtype.val hab)), le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (mem_selEig_one _ _ _ _ _).2 (restriction_mem_invariant_H1 _ (cycU_le l U) y.1)
  · intro x hx
    have hx1 : x.1 ∈ invariantsUnderSubgroupH1 (twist₂ l (ψ * chiO k Ω l O ^ n)) U (cycU l U) := (mem_selEig_one _ _ _ _ _).1 hx
    obtain ⟨κ, γ, hκ, hs, hk, -⟩ := gammaGen k Ω l U hUc hg hχ
    obtain ⟨y, hy⟩ := resZl l O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (qoFacts l O).2.1
      (cycU l U) U (cycU_le l U) hUc κ hκ hs hk hx1
    have hz : ∀ D ∈ shaFam k Ω l, ∀ (W : Subgroup (G k Ω)) (h : W ≤ cycU l U ⊓ D) (h' : W ≤ U),
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h' y = 0 := by
      intro D hD W h h'
      have h0 := mem_locSel.1 x.2 D hD
      rw [← hy, resU_resU] at h0
      have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h t) h0
      rwa [resU_resU, map_zero] at this
    have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_left : U ⊓ Dec (F := k) A ≤ U) y = 0 := by
      intro A hA
      apply inj_cyc k Ω l O ψ n hn hψo (U ⊓ Dec (F := k) A) (hUc.inter (isClosed_Dec A)) (inf_le_left.trans hg)
        (inf_le_left.trans hψ) (hnt A hA)
      rw [resU_resU, map_zero]
      exact hz _ (Or.inl ⟨A, hA, rfl⟩) (cycU l (U ⊓ Dec (F := k) A)) (fun g hg => ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩) _
    refine ⟨⟨y, mem_locSel.2 ?_⟩, Subtype.ext hy⟩
    rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
    · exact hdec A hA
    · by_cases hA : A.valuation (l : Ω) < 1
      · have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_inf_left U (Ine_le_Dec (F := k) A)) t)
          (hdec A hA)
        rwa [resU_resU, map_zero] at this
      · exact hz _ (Or.inr ⟨A, rfl⟩) (U ⊓ Ine (F := k) A)
          (fun g hg => ⟨⟨hg.1, (places k Ω l A).2.2.2 hA hg.2⟩, hg.2⟩) _
end
end
