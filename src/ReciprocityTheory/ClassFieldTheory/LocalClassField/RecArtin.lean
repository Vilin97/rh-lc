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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsF
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormLimit
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceB

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_maximal_exponent_abelian_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 := by
  let U : Subgroup (GK p K) :=
    { carrier := {g | ∀ χ : charGrp (GK p K), n • χ = 0 → χ.1 (Additive.ofMul g) = 0}
      one_mem' := fun χ _ => map_zero χ.1
      mul_mem' := fun {a b} ha hb χ h => by
        show χ.1 (Additive.ofMul a + Additive.ofMul b) = 0
        rw [map_add (f := _), ha χ h, hb χ h, add_zero]
      inv_mem' := fun {a} ha χ h => by
        show χ.1 (- Additive.ofMul a) = 0
        rw [map_neg, ha χ h, neg_zero] }
  have hU : IsOpen (U : Set (GK p K)) := by
    have h1 : (U : Set (GK p K)) = ⋂ χ : {χ : charGrp (GK p K) // n • χ = 0},
        {g : GK p K | χ.1.1 (Additive.ofMul g) = 0} := by
      ext g
      rw [Set.mem_iInter]
      exact ⟨fun h χ => h χ.1 χ.2, fun h χ hχ => h ⟨χ, hχ⟩⟩
    rw [h1]
    exact isOpen_iInter_of_finite fun χ => IsLocallyConstant.isOpen_fiber χ.1.2 0
  obtain ⟨L, hKL, hLfin, hLU⟩ := exists_subG_eq_of_isOpen hK U hU
  refine ⟨L, ⟨hKL, hLfin, ?_⟩, fun χ => ⟨fun hχ => ?_, fun hχ g hg => ?_⟩⟩
  · rw [hLU, commutator_def, Subgroup.commutator_le]
    intro a _ b _ χ _
    show χ.1 (Additive.ofMul a + Additive.ofMul b + - Additive.ofMul a + - Additive.ofMul b) = 0
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_neg, map_neg]
    abel
  · refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
    show n • χ.1 x = 0
    rw [← map_nsmul]
    refine hχ (Additive.toMul x ^ n) ?_
    rw [hLU]
    intro ψ hψ
    show ψ.1 (n • x) = 0
    rw [map_nsmul]
    exact congrArg (fun f : charGrp (GK p K) => f.1 x) hψ
  · rw [hLU] at hg
    exact hg χ hχ

theorem exists_conj {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K)
    (σ : GK p K₀) :
    ∃ c : GK p K →* GK p K, Continuous c ∧ ∀ g, resGK h₀ (c g) = σ * resGK h₀ g * σ⁻¹ := by
  have hn : (subG p K₀ K).Normal := subG_normal_of_stable hK₀
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h₀
  refine ⟨(e.symm.toMonoidHom.comp (MulAut.conjNormal σ : MulAut (subG p K₀ K)).toMonoidHom).comp e.toMonoidHom, ?_, ?_⟩
  · refine hc'.comp (Continuous.comp ?_ hc)
    refine Continuous.subtype_mk (f := fun h : subG p K₀ K => σ * (h : GK p K₀) * σ⁻¹) ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · intro g
    show resGK h₀ (e.symm (MulAut.conjNormal σ (e g))) = _
    rw [← he (e.symm _), e.apply_symm_apply, MulAut.conjNormal_apply, he]

theorem maximal_exponent_extension_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := by
  rw [mem_iff_fixed hL.le]
  intro g hg
  obtain ⟨c, hc, hcg⟩ := exists_conj h₀ hK₀ σ⁻¹
  suffices hmem : c g ∈ subG p K L by
    have h1 : resGK h₀ (c g) x = x := hmem x hx
    rw [hcg, inv_inv] at h1
    have h3 : σ ((σ⁻¹ * resGK h₀ g * σ) x) = g (σ x) := by
      show σ (σ⁻¹ (g (σ x))) = g (σ x)
      exact σ.apply_symm_apply _
    rw [h1] at h3
    exact h3.symm
  by_contra hcon
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL (c g) hcon
  let χ' : charGrp (GK p K) := ⟨χ.1.comp (MonoidHom.toAdditive c),
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp_continuous hc⟩
  have hχ' : n • χ' = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    exact congrArg (fun f : charGrp (GK p K) => f.1 (MonoidHom.toAdditive c y)) ((hL' χ).1 hχ)
  exact hne ((hL' χ').2 hχ' g hg)

theorem mem_subG_adjoin (S : Set (PadicAlgCl p)) (g : GK p K) (h : ∀ x ∈ S, g x = x) :
    g ∈ subG p K (IntermediateField.adjoin ℚ_[p] S) := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap x => exact (g.restrictScalars ℚ_[p]).commutes x
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem isAbelian_cyclotomic_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hfinS : {ζ : PadicAlgCl p | ζ ^ n = 1}.Finite := by
    have h1 : {ζ : PadicAlgCl p | ζ ^ n = 1} = ↑(Polynomial.nthRootsFinset n (1 : PadicAlgCl p)) := by
      ext ζ
      simp [Polynomial.mem_nthRootsFinset hn]
    rw [h1]
    exact Finset.finite_toSet _
  refine ⟨le_sup_left, ?_, ?_⟩
  · have := hK
    have := hfinS.to_subtype
    have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact IntermediateField.finiteDimensional_sup _ _
  · rw [subG_sup, commutator_def, Subgroup.commutator_le]
    intro σ _ τ _
    refine mem_subG_adjoin _ _ fun ζ hζ => ?_
    have hζ' : ζ ^ n = 1 := hζ
    rw [cycN_spec ⁅σ, τ⁆ ζ hζ', map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _),
      Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ', pow_one]

theorem isSolvable_of_abelian_tower {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := by
  have h2 : derivedSeries (GK p K) 2 ≤ subG p K L := by
    have h1 : derivedSeries (GK p K) 1 ≤ subG p K M := hM.comm
    change ⁅derivedSeries (GK p K) 1, derivedSeries (GK p K) 1⁆ ≤ subG p K L
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← range_resGK hM.le] at hg₁ hg₂
    obtain ⟨a, rfl⟩ := hg₁
    obtain ⟨b, rfl⟩ := hg₂
    have h3 : ⁅a, b⁆ ∈ subG p M L :=
      hL.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    rw [← map_commutatorElement]
    intro x hx
    exact h3 x hx
  refine ⟨⟨2, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (subG p K L)), eq_bot_iff, Subgroup.map_le_iff_le_comap]
  intro g hg
  show QuotientGroup.mk' _ g ∈ (⊥ : Subgroup _)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 (h2 hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem card_char_torsion {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) :
    Nat.card {χ : charGrp (GK p K) // n • χ = 0} = (powMonoidHom n : Kˣ →* Kˣ).range.index :=
  card_character_n_torsion hn hμ

theorem exists_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 :=
  exists_maximal_exponent_abelian_extension hK hfin

theorem maxExp_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := maximal_exponent_extension_stable h₀ hK₀ hL hL' σ x hx

theorem normGrp_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K)
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) :
    normGrp p K L = (powMonoidHom n : Kˣ →* Kˣ).range := by
  have hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤ normGrp p K L := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsRecip p K L (a ^ n) 1 := by
      intro χ hχ
      rw [pairK_pow, ← pairK_nsmul, (hL' χ).1 hχ, pairK_zero]
      exact map_zero χ.1
    exact (h1.mem_subG_iff hK hL).1 (subG p K L).one_mem
  have hidx : (normGrp p K L).index = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
    rw [index_normGrp hK hL, ← card_trivOn hL, ← card_char_torsion hn hμ]
    exact Nat.card_congr (Equiv.subtypeEquivRight hL')
  have hfi := finiteIndex_range_pow hK hn
  have h2 := Subgroup.relIndex_mul_index hle
  rw [hidx] at h2
  have h3 : (powMonoidHom n : Kˣ →* Kˣ).range.relIndex (normGrp p K L) = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero) (by rw [h2, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hle

theorem isAbLK_cyclotomic (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := isAbelian_cyclotomic_extension hK hn

theorem isSolvable_of_ab_of_ab {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := isSolvable_of_abelian_tower hM hL

theorem exists_unit_ofK (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ u : Kˣ, ofK p K (Additive.ofMul u) = x :=
  ⟨unitOf p K ⟨x, hx⟩, Units.ext rfl⟩

theorem ofK_injective' : Injective (ofK p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

theorem exists_normGrp_le_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K E ∧ normGrp p K E ≤ (powMonoidHom n : Kˣ →* Kˣ).range := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1} := ⟨_, rfl⟩
  have hM : IsAbLK p K M := hMdef ▸ isAbLK_cyclotomic hK hn
  have hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ M := fun ζ hζ => by
    rw [hMdef]
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _ hζ)
  have hfinM := hM.fin
  have hfin : Finite {χ : charGrp (GK p M) // n • χ = 0} := by
    apply Nat.finite_of_card_ne_zero
    rw [card_char_torsion hn hμ]
    exact (finiteIndex_range_pow hfinM hn).index_ne_zero
  obtain ⟨L, hL, hL'⟩ := exists_maxExp hfinM hn hfin
  have hMst : ∀ (σ : GK p K), ∀ x ∈ M, σ x ∈ M := (subG_normal_iff hM.le).1 hM.normal
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := fun σ x hx => maxExp_stable hM.le hMst hL hL' σ x hx
  have : (subG p K L).Normal := subG_normal_of_stable hst
  have hKL : K ≤ L := hM.le.trans hL.le
  have hsol := isSolvable_of_ab_of_ab hM hL
  obtain ⟨E, hE, hEL, hE'⟩ := exists_maxAb hL.fin hKL
  refine ⟨E, hE, ?_⟩
  rw [← normGrp_eq_of_soluble hK hL.fin hKL hsol hE hEL hE']
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_normGrp_iff p K L x).1 hx
  rw [← normHom_trans hL.fin hM.le hL.le y hy] at hxy
  obtain ⟨z, hz⟩ := exists_unit_ofK _ (normHom_mem hL.fin hL.le y hy)
  have hzN : z ∈ normGrp p M L := (mem_normGrp_iff p M L z).2 ⟨y, hy, hz.symm⟩
  rw [normGrp_maxExp hfinM hn hμ hL hL'] at hzN
  obtain ⟨w, rfl⟩ := hzN
  obtain ⟨u, hu⟩ := exists_unit_ofK (K := K) _ (normHom_mem hfinM hM.le _ (ofK_mem p M (Additive.ofMul w)))
  refine ⟨u, ?_⟩
  apply Additive.ofMul.injective
  apply ofK_injective' (K := K)
  rw [← hxy, ← hz]
  show ofK p K (n • Additive.ofMul u) = normHom p K M (ofK p M (n • Additive.ofMul w))
  rw [map_nsmul, map_nsmul, map_nsmul, hu]

theorem existence (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ) (hH : H.FiniteIndex) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ normGrp p K L = H := by
  obtain ⟨E, hE, hEle⟩ := exists_normGrp_le_pow hK (n := H.index) (Nat.pos_of_ne_zero hH.index_ne_zero)
  obtain ⟨L₀, h1, -, h2⟩ := exists_normGrp_eq_of_le hK hE H (hEle.trans (by
    rintro _ ⟨a, rfl⟩; exact Subgroup.pow_index_mem H a))
  exact ⟨L₀, h1, h2⟩

theorem exists_not_mem_UKi (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (ha : a ≠ 1) : ∃ i, a ∉ UKi p K i := by
  have hε : 0 < ‖((a : K) : PadicAlgCl p) - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    exact ha (Units.ext (Subtype.ext h))
  have he : (0 : ℝ) < eK p K := by exact_mod_cast eK_pos p K hK
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hq1 : (p : ℝ) ^ (- 1 / (eK p K : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (div_neg_of_neg_of_pos (by norm_num) he)
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε hq1
  refine ⟨i, fun hx => absurd (lt_of_le_of_lt ((mem_UKi_iff p K i a).1 hx).2 ?_) (lt_irrefl _)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le] at hi
  convert hi using 2
  ring

theorem eq_one_of_forall_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (h : ∀ L, IsAbLK p K L → a ∈ normGrp p K L) : a = 1 := by
  by_contra ha
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  obtain ⟨i, hi⟩ := exists_not_mem_UKi hK a ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (vK p K a).natAbs + 1 := ⟨_, rfl⟩
  have hopen : IsOpen ((UKi p K i ⊔ Subgroup.zpowers (π ^ m) : Subgroup Kˣ) : Set Kˣ) :=
    Subgroup.isOpen_mono le_sup_left (isOpen_UKi i)
  have hfi : (UKi p K i ⊔ Subgroup.zpowers (π ^ m)).FiniteIndex :=
    finiteIndex_of_isOpen_of_vK hK _ hopen (x := π ^ m)
      ((le_sup_right : _ ≤ UKi p K i ⊔ _) (Subgroup.mem_zpowers _)) (by rw [vK_pow, hπ, hm]; positivity)
  obtain ⟨L, hL, hLH⟩ := existence hK _ hfi
  have haH : a ∈ UKi p K i ⊔ Subgroup.zpowers (π ^ m) := hLH ▸ h L hL
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 haH
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hu0 : vK p K u = 0 := (mem_UK_iff p K hK u).1 ((mem_UKi_iff p K i u).1 hu).1
  have hv : vK p K (u * (π ^ m) ^ k) = k * m := by
    rw [vK_mul, hu0, vK_zpow, vK_pow, hπ]; ring
  rw [hv] at hm
  have hk : k = 0 := by
    by_contra hk
    have h1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hm
    nlinarith
  rw [hk, zpow_zero, mul_one] at hi
  exact hi hu

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.RecArtin

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_artin_hom (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a →
    ∀ L, IsAbLK p K L → IsRecip p K L a g := by
  classical
  let γ : IntermediateField ℚ_[p] (PadicAlgCl p) → Kˣ → GK p K := fun L a =>
    if h : IsAbLK p K L then (exists_isRecip h a).choose else 1
  have hγ : ∀ L, IsAbLK p K L → ∀ a, IsRecip p K L a (γ L a) := by
    intro L hL a
    simp only [γ, dif_pos hL]
    exact (exists_isRecip hL a).choose_spec
  obtain ⟨f, hf⟩ := exists_hom_GKab hK γ
    (fun L hL a b => IsRecip.unique hL (hγ L hL (a * b)) ((hγ L hL a).mul (hγ L hL b)))
    (fun L L' hL hL' hle a => IsRecip.unique hL (hγ L hL a) ((hγ L' hL' a).of_le hle))
  exact ⟨f, fun a g hg L hL => (hγ L hL a).congr (hf L hL a g hg)⟩

theorem isFrob_of_forall_Kn (hK : FiniteDimensional ℚ_[p] K) (g : GK p K)
    (h : ∀ n, 0 < n → (frobK p K)⁻¹ * g ∈ subG p K (Kn p K n)) : IsFrob p K g := by
  rw [isFrob_iff hK]
  intro ζ m hm hζ
  obtain ⟨n, hn, hζn⟩ := (mem_Kur_iff hK ζ).1 (mem_Kur_of_pow hK hm hζ)
  have h1 : frobK p K ζ = g ζ :=
    (mk_eq_mk_iff (M := Kn p K n) (frobK p K) g).1 (QuotientGroup.eq.2 (h n hn)) ζ hζn
  rw [← h1]
  exact (isFrob_iff hK _).1 (isFrob_frobK hK) ζ m hm hζ

theorem isFrob_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (g : GK p K)
    (h : ∀ L, IsAbLK p K L → IsRecip p K L π g) : IsFrob p K g :=
  isFrob_of_forall_Kn hK g fun _ hn =>
    IsRecip.unique (isAbLK_Kn hK hn) (isRecip_uniformiser_Kn hK hn π hπ) (h _ (isAbLK_Kn hK hn))

theorem IsRecip.inv_mul_mem (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a b : Kˣ} {g g' : GK p K}
    (h : IsRecip p K L a g) (h' : IsRecip p K L b g') : g⁻¹ * g' ∈ subG p K L ↔ a⁻¹ * b ∈ normGrp p K L := by
  obtain ⟨k, hk⟩ := exists_isRecip hL (a⁻¹ * b)
  have h1 : IsRecip p K L b (g * k) := by
    have := h.mul hk
    rwa [mul_inv_cancel_left] at this
  have h2 : (g * k)⁻¹ * g' ∈ subG p K L := IsRecip.unique hL h1 h'
  rw [← hk.mem_subG_iff hK hL]
  have h3 : g⁻¹ * g' = k * ((g * k)⁻¹ * g') := by group
  rw [h3]
  exact Subgroup.mul_mem_cancel_right _ h2

theorem isArtinK_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (Art : Kˣ →* GKab p K)
    (h : ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a → ∀ L, IsAbLK p K L → IsRecip p K L a g) :
    IsArtinK p K Art := by
  have hsurj : ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧
      g'⁻¹ * g ∈ subG p K L := by
    intro L hL g
    obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
    obtain ⟨g', hg'⟩ := toAbK_surjective (Art a)
    exact ⟨a, g', hg', IsRecip.unique hL (h a g' hg' L hL) ha⟩
  refine ⟨?_, ?_, (denseRange_GKab_iff hK Art).2 hsurj, ?_, fun L hL => ⟨hsurj L hL, ?_⟩⟩
  · rw [continuous_GKab_iff hK]
    intro L hL x
    have hopen : IsOpen ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ)) :=
      (isOpen_normGrp hK hL.fin hL.le).preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ) := by
      show x⁻¹ * x ∈ normGrp p K L
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hx] with y hy g g' hg hg'
    exact (IsRecip.inv_mul_mem hK hL (h x g hg L hL) (h y g' hg' L hL)).2 hy
  · rw [injective_iff_map_eq_one]
    intro a ha
    refine eq_one_of_forall_mem_normGrp hK a fun L hL => ?_
    have h1 : toAbK p K 1 = Art a := by rw [map_one, ha]
    exact ((h a 1 h1 L hL).mem_subG_iff hK hL).1 (one_mem _)
  · intro π hπ g hg
    exact isFrob_of_isRecip hK π hπ g (h π g hg)
  · intro x g hg
    exact (h x g hg L hL).mem_subG_iff hK hL

theorem exists_isArtinK (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, IsArtinK p K Art := by
  obtain ⟨Art, h⟩ := exists_artin_hom hK
  exact ⟨Art, isArtinK_of_isRecip hK Art h⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
end
