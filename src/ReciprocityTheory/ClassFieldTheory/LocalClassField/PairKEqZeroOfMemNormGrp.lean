module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecAbA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecAbC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunct
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsE
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.RecUnr

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_ur_lift (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ, IsLocallyConstant t ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let f : GK p K → QZ := fun g => χ.1 (Additive.ofMul g)
  have hf : IsLocallyConstant f := χ.2
  have hfq : ∀ g : GK p K, f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out = f g := by
    intro g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (subG p K (MaximalUnramifiedExtension p K)) g
    rw [hn]
    show χ.1 (Additive.ofMul g + Additive.ofMul n.1) = _
    rw [map_add (f := _), hχ n.1 n.2, add_zero]
  have hloc : IsLocallyConstant fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out := by
    intro s
    rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h0 : (QuotientGroup.mk : GK p K → GalLK p K (MaximalUnramifiedExtension p K)) ⁻¹'
        ((fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out) ⁻¹' s) = f ⁻¹' s := by
      ext g
      show f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out ∈ s ↔ f g ∈ s
      rw [hfq]
    rw [h0]
    exact hf s
  refine ⟨fun q => sec (f q.out), hloc.comp sec, fun g => ?_⟩
  rw [hsec]
  exact hfq g


variable (p K) in
noncomputable def urOfK (a : Kˣ) : (urT p K).V :=
  toLayer p ⟨ofK p K (Additive.ofMul a), le_Kur (K := K) (ofK_mem p K _)⟩

theorem exists_ur_cocycle (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ) (z : (urT p K).coch.X 2)
      (hz : (urT p K).coch.d 2 z = 0), IsLocallyConstant t ∧
      (∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • urOfK p K a) ∧
      pairBr p K a χ = (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) := by
  obtain ⟨t, ht, htχ⟩ := exists_ur_lift χ hχ
  have hex : ∀ g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K), ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (g 0)
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (g 1)
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [← hσ, ← hτ, ← QuotientGroup.mk_mul, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, htχ, htχ, htχ,
        ofMul_mul, map_add, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • urOfK p K a :=
    (hmc.comp fun k : ℤ => k • urOfK p K a).continuous
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • urOfK p K a, hzc⟩
  have hinv := (layer_invariant_iff (urOfK p K a)).2 (ofK_mem p K _)
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hm, hm, hm, hm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
      ring
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • urOfK p K a) - m ![g 0 * g 1, g 2] • urOfK p K a +
      m ![g 0, g 1 * g 2] • urOfK p K a - m ![g 0, g 1] • urOfK p K a = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨t, m, z, hz, ht, htχ, hm, fun _ => rfl, ?_⟩
  refine IsPairClass.unique (isPairClass_pairBr a χ)
    ⟨fun g => t (QuotientGroup.mk g), fun g => m fun i => QuotientGroup.mk (g i),
      (layerInf p K (MaximalUnramifiedExtension p K)).hom.f 2 z, by rw [← (layerInf p K (MaximalUnramifiedExtension p K)).hom.comm, hz, map_zero],
      ht.comp_continuous continuous_quot_mk, htχ, fun g => hm _, fun g => rfl, rfl⟩

theorem pairK_uniformiser_unr (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K π χ = χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, h⟩ := exists_ur_cocycle π χ hχ
  have h1 : (eK p K : ℝ) * vbar p (urOfK p K π).1 = 1 := by
    have h2 := vOn_spec p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩
    have h3 : vOn p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩ = 1 := hπ
    rw [h3, Int.cast_one] at h2
    exact h2.symm
  unfold pairK
  rw [h, invBr_layerInf hK, isInv_invUr hK (urOfK p K π) t m z hz (ofK_mem p K _) h1 ht hm hzm]
  exact htχ (frobK p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem TrivOn.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') {χ : charGrp (GK p K)} (hχ : TrivOn p K L χ) : TrivOn p K L' χ :=
  fun g hg => hχ g fun x hx => hg x (h hx)

theorem IsRecip.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') {a : Kˣ} {g : GK p K} (hg : IsRecip p K L' a g) :
    IsRecip p K L a g := fun χ hχ => hg χ (hχ.of_le h)

theorem IsRecip.mul {a b : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g) (h' : IsRecip p K L b g') :
    IsRecip p K L (a * b) (g * g') := fun χ hχ => by
  rw [pairK_mul, ← h χ hχ, ← h' χ hχ, ofMul_mul, map_add (f := _)]

theorem IsRecip.congr {a : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g) (hg : g⁻¹ * g' ∈ subG p K L) :
    IsRecip p K L a g' := fun χ hχ => by
  rw [← h χ hχ, show g' = g * (g⁻¹ * g') by group, ofMul_mul, map_add (f := _), hχ _ hg, add_zero]

theorem exists_quot_data (hL : IsAbLK p K L) : ∃ (A : Type) (_ : AddCommGroup A) (_ : Finite A) (π : Additive (GK p K) →+ A),
    Surjective π ∧ (IsLocallyConstant fun g : GK p K => π (Additive.ofMul g)) ∧ Nat.card A = degLK p K L ∧
    ∀ g : GK p K, π (Additive.ofMul g) = 0 ↔ g ∈ subG p K L := by
  have := hL.normal
  have := discreteTopology_GalLK (K := K) hL.fin
  refine ⟨Additive (GalLK p K L), quotAddCommGroup (subG p K L) hL.comm,
    finite_GalLK (K := K) hL.fin, MonoidHom.toAdditive (QuotientGroup.mk' (subG p K L)), ?_, ?_, ?_, ?_⟩
  · exact fun x => (QuotientGroup.mk'_surjective (subG p K L) (Additive.toMul x)).imp fun g hg => congrArg Additive.ofMul hg
  · exact (IsLocallyConstant.of_discrete (fun x : GalLK p K L => Additive.ofMul x)).comp_continuous
      QuotientGroup.continuous_mk
  · rfl
  · intro g
    exact QuotientGroup.eq_one_iff g

theorem exists_char_ne_zero (hL : IsAbLK p K L) (g : GK p K) (hg : g ∉ subG p K L) :
    ∃ χ : charGrp (GK p K), TrivOn p K L χ ∧ χ.1 (Additive.ofMul g) ≠ 0 := by
  obtain ⟨A, _, _, π, hπ, hc, -, hker⟩ := exists_quot_data hL
  obtain ⟨χ, h1, h2⟩ := exists_character_ne_zero_of_quotient hc g (fun h => hg ((hker g).1 h))
  exact ⟨χ, fun g hg => h1 g ((hker g).2 hg), h2⟩

theorem card_trivOn (hL : IsAbLK p K L) :
    Nat.card {χ : charGrp (GK p K) // TrivOn p K L χ} = degLK p K L := by
  obtain ⟨A, _, _, π, hπ, hc, hcard, hker⟩ := exists_quot_data hL
  rw [← hcard, ← card_characters_of_finite_quotient hc hπ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun χ =>
    ⟨fun h g hg => h g ((hker g).1 hg), fun h g hg => h g ((hker g).2 hg)⟩)

theorem exists_eval (hL : IsAbLK p K L) (f : charGrp (GK p K) →+ QZ) :
    ∃ g : GK p K, ∀ χ, TrivOn p K L χ → χ.1 (Additive.ofMul g) = f χ := by
  obtain ⟨A, _, _, π, hπ, hc, -, hker⟩ := exists_quot_data hL
  obtain ⟨g, hg⟩ := exists_element_evaluating_characters hc hπ f
  exact ⟨g, fun χ hχ => hg χ fun g hg => hχ g ((hker g).1 hg)⟩

theorem IsRecip.unique (hL : IsAbLK p K L) {a : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g)
    (h' : IsRecip p K L a g') : g⁻¹ * g' ∈ subG p K L := by
  by_contra hn
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL _ hn
  apply hne
  rw [ofMul_mul, map_add (f := _), ofMul_inv, map_neg, h χ hχ, h' χ hχ, neg_add_cancel]

theorem exists_isRecip (hL : IsAbLK p K L) (a : Kˣ) : ∃ g : GK p K, IsRecip p K L a g :=
  exists_eval hL
    { toFun := fun χ => pairK p K a χ
      map_zero' := pairK_zero a
      map_add' := pairK_add a }

theorem index_normGrp_le (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) :
    (normGrp p K L).index ≠ 0 ∧ (normGrp p K L).index ≤ degLK p K L := by
  refine ⟨(finiteIndex_normGrp hK hL.fin hL.le).index_ne_zero, ?_⟩
  induction hn : degLK p K L using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    by_cases hall : ∀ g : GK p K, g ∈ subG p K L
    · have h1 : L ≤ K := by
        have := (subG_le_iff (L' := K) hL.le).1 fun s _ => hall s
        rwa [sup_idem] at this
      have h2 : L = K := le_antisymm h1 hL.le
      rw [h2, normGrp_self, Subgroup.index_top]
      exact hn ▸ degLK_pos hL.fin
    · push Not at hall
      obtain ⟨g, hg⟩ := hall
      obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL g hg
      obtain ⟨M, hM, hML, hlt, hdeg, hle⟩ := index_normGrp_le_step hK hL g χ hχ hne
      have h3 := ih _ (hn ▸ hlt) hM hML rfl
      calc (normGrp p K L).index ≤ (normGrp p M L).index * degLK p K M := hle
        _ ≤ degLK p M L * degLK p K M := Nat.mul_le_mul_right _ h3
        _ = n := by rw [← hn, hdeg, mul_comm]

theorem pairK_eq_zero_of_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (a : Kˣ) (ha : a ∈ normGrp p K L)
    (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : pairK p K a χ = 0 :=
  local_pairing_eq_zero_of_mem_normGroup hK hL.fin hL.le a ha χ hχ

theorem IsRecip.inv {a : Kˣ} {g : GK p K} (h : IsRecip p K L a g) : IsRecip p K L a⁻¹ g⁻¹ := fun χ hχ => by
  rw [pairK_inv, ← h χ hχ, ofMul_inv, map_neg]

theorem isRecip_one_of_mem {g : GK p K} (hg : g ∈ subG p K L) : IsRecip p K L 1 g := fun χ hχ => by
  rw [pairK_one, hχ g hg]


variable (p K L) in
def recipImage (H : Subgroup Kˣ) : Subgroup (GK p K) where
  carrier := {g | ∃ a ∈ H, IsRecip p K L a g}
  one_mem' := ⟨1, H.one_mem, isRecip_one_of_mem (subG p K L).one_mem⟩
  mul_mem' := fun ⟨a, ha, h⟩ ⟨b, hb, h'⟩ => ⟨a * b, H.mul_mem ha hb, h.mul h'⟩
  inv_mem' := fun ⟨a, ha, h⟩ => ⟨a⁻¹, H.inv_mem ha, h.inv⟩

theorem exists_field_recipImage (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (H : Subgroup Kˣ) :
    ∃ L₀ : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L₀ ∧ L₀ ≤ L ∧ subG p K L₀ = recipImage p K L H := by
  have hle : subG p K L ≤ recipImage p K L H := fun g hg => ⟨1, H.one_mem, isRecip_one_of_mem hg⟩
  obtain ⟨L₀, h0, -, he⟩ := exists_subG_eq_of_isOpen hK _ (Subgroup.isOpen_mono hle (isOpen_subG hL.fin))
  have h1 : L₀ ≤ L := by
    have := (subG_le_iff (L' := L) h0).1 (he ▸ hle)
    rwa [sup_eq_right.2 hL.le] at this
  exact ⟨L₀, hL.of_le h0 h1, h1, he⟩

theorem exists_isRecip_of_gal (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (g : GK p K) : ∃ a : Kˣ, IsRecip p K L a g := by
  obtain ⟨L₀, hL₀, hle, he⟩ := exists_field_recipImage hK hL ⊤
  by_contra hcon
  have hg : g ∉ subG p K L₀ := by
    rw [he]
    rintro ⟨a, -, ha⟩
    exact hcon ⟨a, ha⟩
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL₀ g hg
  have h0 : χ = 0 := eq_zero_of_pairK_eq_zero hK χ fun a => by
    obtain ⟨g', hg'⟩ := exists_isRecip hL a
    rw [← hg' χ (hχ.of_le hle)]
    exact hχ g' (he ▸ ⟨a, trivial, hg'⟩)
  exact hne (by rw [h0]; rfl)

theorem exists_recipHom (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) [(subG p K L).Normal] :
    ∃ φ : Kˣ →* GalLK p K L, Surjective φ ∧ ∀ a g, IsRecip p K L a g ↔ φ a = QuotientGroup.mk g := by
  choose γ hγ using fun a => exists_isRecip hL a
  refine ⟨MonoidHom.mk' (fun a => QuotientGroup.mk (γ a)) (fun a b => ?_), ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (IsRecip.unique hL (hγ _) ((hγ a).mul (hγ b)))
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
      exact ⟨a, QuotientGroup.eq.2 (IsRecip.unique hL (hγ a) ha)⟩
  · intro a g
    constructor
    · intro h
      exact QuotientGroup.eq.2 (IsRecip.unique hL (hγ a) h)
    · intro h
      exact (hγ a).congr (QuotientGroup.eq.1 h)

theorem IsRecip.mem_subG_of_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a : Kˣ} {g : GK p K}
    (h : IsRecip p K L a g) (ha : a ∈ normGrp p K L) : g ∈ subG p K L := by
  by_contra hg
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL g hg
  exact hne ((h χ hχ).trans (pairK_eq_zero_of_mem_normGrp hK hL a ha χ hχ))

theorem recipHom_ker (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) [(subG p K L).Normal] (φ : Kˣ →* GalLK p K L)
    (hs : Surjective φ) (hφ : ∀ a g, IsRecip p K L a g ↔ φ a = QuotientGroup.mk g) :
    φ.ker = normGrp p K L ∧ (normGrp p K L).index = degLK p K L := by
  have hle : normGrp p K L ≤ φ.ker := fun a ha => by
    obtain ⟨g, hg⟩ := exists_isRecip hL a
    rw [MonoidHom.mem_ker, (hφ a g).1 hg]
    exact (QuotientGroup.eq_one_iff g).2 (hg.mem_subG_of_mem_normGrp hK hL ha)
  have hk : φ.ker.index = degLK p K L := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top]
    rfl
  obtain ⟨h0, h1⟩ := index_normGrp_le hK hL
  have h2 : (normGrp p K L).index = degLK p K L :=
    le_antisymm h1 (hk ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Subgroup.index_dvd_of_le hle))
  refine ⟨le_antisymm ?_ hle, h2⟩
  have h3 := Subgroup.relIndex_mul_index hle
  rw [hk, h2] at h3
  have h4 : (normGrp p K L).relIndex φ.ker = 1 :=
    Nat.eq_of_mul_eq_mul_right (degLK_pos hL.fin) (by rw [h3, one_mul])
  exact Subgroup.relIndex_eq_one.1 h4

theorem IsRecip.mem_subG_iff (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a : Kˣ} {g : GK p K} (h : IsRecip p K L a g) :
    g ∈ subG p K L ↔ a ∈ normGrp p K L := by
  have := hL.normal
  obtain ⟨φ, hs, hφ⟩ := exists_recipHom hK hL
  rw [← (recipHom_ker hK hL φ hs hφ).1, MonoidHom.mem_ker, (hφ a g).1 h]
  exact (QuotientGroup.eq_one_iff g).symm

theorem index_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) : (normGrp p K L).index = degLK p K L := by
  have := hL.normal
  obtain ⟨φ, hs, hφ⟩ := exists_recipHom hK hL
  exact (recipHom_ker hK hL φ hs hφ).2

theorem exists_normGrp_eq_of_le (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (H : Subgroup Kˣ) (hH : normGrp p K L ≤ H) :
    ∃ L₀ : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L₀ ∧ L₀ ≤ L ∧ normGrp p K L₀ = H := by
  obtain ⟨L₀, hL₀, hle, he⟩ := exists_field_recipImage hK hL H
  refine ⟨L₀, hL₀, hle, ?_⟩
  ext a
  obtain ⟨g, hg⟩ := exists_isRecip hL a
  rw [← (hg.of_le hle).mem_subG_iff hK hL₀, he]
  constructor
  · rintro ⟨a', ha', hg'⟩
    have h1 : IsRecip p K L (a * a'⁻¹) 1 := by
      have := hg.mul hg'.inv
      rwa [mul_inv_cancel] at this
    have h2 : a * a'⁻¹ ∈ H := hH ((h1.mem_subG_iff hK hL).1 (subG p K L).one_mem)
    have := H.mul_mem h2 ha'
    rwa [inv_mul_cancel_right] at this
  · intro ha
    exact ⟨a, ha, hg⟩

theorem isRecip_uniformiser_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (π : Kˣ) (hπ : vK p K π = 1) :
    IsRecip p K (Kn p K n) π (frobK p K) := fun χ hχ =>
  (pairK_uniformiser_unr hK π hπ χ (hχ.of_le (Kn_le_Kur hn))).symm

theorem stable_inv_of_stable {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (σ : GK p K)
    (h : ∀ x ∈ M, σ x ∈ M) : ∀ x ∈ M, σ⁻¹ x ∈ M := by
  let f : M →ₐ[ℚ_[p]] M := AlgHom.codRestrict
    (((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp M.val)
    M.toSubalgebra (fun x => h x.1 x.2)
  have hf := Algebra.IsAlgebraic.algHom_bijective f
  intro x hx
  obtain ⟨y, hy⟩ := hf.2 ⟨x, hx⟩
  have h1 : σ y.1 = x := congrArg Subtype.val hy
  rw [← h1]
  show (σ⁻¹ * σ) y.1 ∈ M
  rw [inv_mul_cancel]
  exact y.2

theorem exists_conjGK {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (h : K ≤ M) (σ : GK p K)
    (hσ : ∀ x ∈ M, σ x ∈ M) :
    ∃ c : GK p M →* GK p M, Continuous c ∧ ∀ g, resGK h (c g) = σ * resGK h g * σ⁻¹ := by
  have hinv := stable_inv_of_stable hM σ hσ
  have hex : ∀ g : GK p M, ∃ g' : GK p M, resGK h g' = σ * resGK h g * σ⁻¹ := fun g => by
    have : σ * resGK h g * σ⁻¹ ∈ (resGK h).range := by
      rw [range_resGK h]
      intro x hx
      show σ (g (σ⁻¹ x)) = x
      rw [show g (σ⁻¹ x) = σ⁻¹ x from g.commutes ⟨_, hinv x hx⟩]
      show (σ * σ⁻¹) x = x
      rw [mul_inv_cancel]; rfl
    exact this
  choose c hc using hex
  refine ⟨MonoidHom.mk' c fun a b => resGK_injective h ?_, ?_, hc⟩
  · rw [map_mul, hc, hc, hc, map_mul]; group
  · rw [(isClosedEmbedding_resGK h).isInducing.continuous_iff]
    have : (resGK h ∘ (MonoidHom.mk' c fun a b => resGK_injective h (by rw [map_mul, hc, hc, hc, map_mul]; group))) =
        fun g => σ * resGK h g * σ⁻¹ := funext hc
    rw [this]
    exact (continuous_const.mul (resGK_continuous h)).mul continuous_const

theorem IsRecip.conj (hK : FiniteDimensional ℚ_[p] K) {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (h : K ≤ M) (σ : GK p K)
    (hM : ∀ x ∈ M, σ x ∈ M) (hL : ∀ x ∈ L, σ x ∈ L) (hL' : ∀ x ∈ L, σ⁻¹ x ∈ L) {b b' : Mˣ} (hb : ((b' : M) : PadicAlgCl p) = σ ((b : M) : PadicAlgCl p))
    {g g' : GK p M} (hg' : resGK h g' = σ * resGK h g * σ⁻¹) (hg : IsRecip p M L b g) :
    IsRecip p M L b' g' := by
  have hfd : FiniteDimensional ℚ_[p] M := by assumption
  obtain ⟨c, hcc, hc⟩ := exists_conjGK hfd h σ hM
  intro χ' hχ'
  let χ : charGrp (GK p M) := ⟨χ'.1.comp (MonoidHom.toAdditive c),
    (show IsLocallyConstant fun g : GK p M => χ'.1 (Additive.ofMul g) from χ'.2).comp_continuous hcc⟩
  have hχ : ∀ s s' : GK p M, resGK h s' = σ * resGK h s * σ⁻¹ →
      χ'.1 (Additive.ofMul s') = χ.1 (Additive.ofMul s) := fun s s' hs => by
    rw [resGK_injective h (hs.trans (hc s).symm)]; rfl
  have htriv : TrivOn p M L χ := fun s hs => by
    refine hχ' (c s) fun x hx => ?_
    show resGK h (c s) x = x
    rw [hc]
    show σ (s (σ⁻¹ x)) = x
    rw [hs _ (hL' x hx)]
    show (σ * σ⁻¹) x = x
    rw [mul_inv_cancel]; rfl
  rw [pairK_conj hK hfd h σ hM b b' hb χ χ' hχ, ← hg χ htriv]
  exact hχ g g' hg'

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
end
