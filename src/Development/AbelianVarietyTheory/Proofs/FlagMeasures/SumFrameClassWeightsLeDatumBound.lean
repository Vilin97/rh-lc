module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinorsStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotentStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfMulMem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLeStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  first | exact @GlobalTheory.DegCnt.c_eq_quot_ideals | exact GlobalTheory.DegCnt.c_eq_quot_ideals | (intros; apply GlobalTheory.DegCnt.c_eq_quot_ideals <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.PerDat

theorem sum_le_of_fibres {ι α : Type} [DecidableEq α] (s : Finset ι) (k : ι → α) (f : ι → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hM : ((s.image k).card : ℝ) ≤ M) (h : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => k i = k i₀), f i ≤ B) :
    ∑ i ∈ s, f i ≤ M * B := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := s.image k) (fun i hi => Finset.mem_image_of_mem k hi)]
  refine (Finset.sum_le_card_nsmul _ _ B fun y hy => ?_).trans ?_
  · obtain ⟨i₀, hi, rfl⟩ := Finset.mem_image.1 hy
    exact h i₀ hi
  · rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hM hB

section Carry
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Carr (s : V ≃ₗ[K] V) (A B : FlagD H r) : Prop := ∀ a : Fin (r + 1), s (A.e a) - B.e a ∈ B.Xa a.val

theorem Carr.map_xa {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : Carr s A B) (n : ℕ) {x : V} (hx : x ∈ A.Xa n) :
    s x ∈ B.Xa n := by
  have : A.Xa n ≤ (B.Xa n).comap (s : V →ₗ[K] V) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have := Submodule.add_mem _ (AdaptInv.xa_mono B (le_of_lt hb) (h b.castSucc)) (AdaptInv.e_mem_xa B b hb)
    simpa using this
  exact this hx

theorem Carr.trans {s t : V ≃ₗ[K] V} {A B C : FlagD H r} (h : Carr s A B) (h' : Carr t B C) :
    Carr (t * s) A C := fun a => by
  have := Submodule.add_mem _ (h'.map_xa _ (h a)) (h' a)
  simpa using this

theorem carr_of_sameGr {A B : FlagD H r} (h : SameGr B A) : Carr 1 A B := fun a => h a

theorem carr_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s A B := fun a => by
  rw [h a, sub_self]; exact zero_mem _

theorem carr_inv_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s⁻¹ B A :=
  carr_of_eq fun a => by rw [← h a]; exact s.symm_apply_apply _

theorem carr_of_inN {s : V ≃ₗ[K] V} {A : FlagD H r} (h : A.InN (s : V →ₗ[K] V)) : Carr s A A := fun a => by
  induction a using Fin.lastCases with
  | last => exact GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem h
  | cast b => exact h.2.2.1 b

theorem flagFrameVector_mem_commonSubspace (A B : FlagD H r) (a : Fin (r + 1)) : A.e a ∈ V0 A B := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X A b))

end Carry

section Main
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {e : W →ₗ[K] V} {r : ℕ}

omit [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
theorem finrank_wt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (he : IsEmb F HW e) (hN : Adapt F G 𝔡 N) : Module.finrank K N.Wt = Module.finrank K W := by
  obtain ⟨hfull, hlift, -⟩ := GlobalTheory.DegCnt.NF.geometry K V H hK r N
  have hX : N.F.X = F.X := AdaptInv.x_eq hN.2.1
  have hV : V0 N.F N.F' = V0 F G := AdaptInv.sitesCommonSpace_v0_eq_Vp hN.2.1 hN.2.2
  have hperp : ∀ (w : W) (a : Fin (r + 1)), H.B (F.e a) (e w) = 0 :=
    fun w => (he.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
  have hinj : Function.Injective e := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    refine HW.nondeg w fun y => ?_
    rw [← he.1, hw]; simp
  have h1 : LinearMap.range e ⊓ F.X = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    have : w = 0 := HW.nondeg w fun y => by
      rw [← he.1]
      exact GlobalTheory.UnipStab.orth_X F (fun a => hperp y _) hw
    simp [this]
  have h2 : N.Wt ⊓ F.X = ⊥ := by
    rw [eq_bot_iff, ← hlift.2.1, ← hX]
    rintro x ⟨hx, hx'⟩
    exact ⟨hx, (hfull.2.2.2.2.2.1 x hx').1 (hlift.1 x hx)⟩
  have h3 : N.Wt ⊔ F.X = LinearMap.range e ⊔ F.X := by
    apply le_antisymm
    · refine sup_le (fun x hx => (he.2 x).1 fun a => hlift.1 x hx _ ?_) le_sup_right
      rw [hV]; exact flagFrameVector_mem_commonSubspace F G a
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, hx, hx'⟩ := hfull.2.2.2.2.2.2.2.1 (e w) fun a => by
        have a1 : N.F.e a - F.e a ∈ F.X := AdaptInv.xa_mono F (Nat.lt_succ_iff.1 a.2) (hN.2.1 a)
        have a2 := GlobalTheory.UnipStab.orth_X F (fun a => hperp w _) a1
        simpa [hperp w a] using a2
      have a3 : e w - x ∈ N.Wt ⊔ F.X := by
        refine (sup_le_sup_left (show II N.F N.F' ≤ F.X from hX ▸ inf_le_left) _) (hlift.2.2 _ hx')
      have := Submodule.add_mem _ a3 (Submodule.mem_sup_right (hX ▸ hx))
      simpa using this
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt F.X
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) F.X
  rw [h2, h3] at d1
  rw [h1, LinearMap.finrank_range_of_inj hinj] at d2
  omega

theorem one_class (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F : FlagD H r} {𝔡 : Ideal (𝓞 K)} {g : ℕ} {Λ : Submodule (𝓞 K) V}
    {ι : Type} (s : Finset ι) (G : ι → FlagD H r) (N : ι → NF H r) (G₀ : FlagD H r) (N₀ : NF H r) (hg : 1 ≤ g)
    (he : IsEmb F HW e) (h₀ : Adapt F G₀ 𝔡 N₀) (ht₀ : N₀.IsTerm g Λ)
    (hN : ∀ i ∈ s, Adapt F (G i) 𝔡 (N i) ∧ (N i).IsTerm g Λ ∧ N₀.j = (N i).j ∧ N₀.c = (N i).c ∧ N₀.T = (N i).T ∧
      pairM N₀.F N₀.F' N₀.j = pairM (N i).F (N i).F' (N i).j ∧ datOf F (G i) e g Λ = datOf F G₀ e g Λ)
    (hinj : ∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') :
    ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.NT ^ 2 * ((N₀.Del / N₀.gI g Λ) ^ ((Module.finrank K W : ℝ) / 2) *
      N₀.Del ^ (cf K + 2) * (N₀.Db * N₀.Del * N₀.NT) ^ (10000 * (r + 1) ^ 3)) := by
  have hex : ∀ i ∈ s, ∃ σ : V ≃ₗ[K] V, F.InN (σ : V →ₗ[K] V) ∧
      ∀ a, σ (N₀.F.e a) = (N i).F.e a ∧ σ (N₀.F'.e a) = (N i).F'.e a := fun i hi => by
    obtain ⟨a1, -, a2, a3, a4, a5, -⟩ := hN i hi
    exact GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent K V H hK r F N₀ (N i) h₀.2.1 a1.2.1 a2 a3 a4 a5
  choose! σ hσ hσe using hex
  have hcan : ∀ i, σ i • ((σ i)⁻¹ • Λ) = Λ := fun i => smul_inv_smul _ _
  have hmove : ∀ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.om ((σ i)⁻¹ • Λ) ∧ N₀.IsTerm g ((σ i)⁻¹ • Λ) := fun i hi => by
    obtain ⟨a1, a2, -⟩ := hN i hi
    obtain ⟨N', b1, -, -, -, b2, -, b3⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N₀ (σ i) ((mem_isomGrp H _).2 (hσ i hi).1)
    obtain ⟨c1, c2, -⟩ := b3 g ((σ i)⁻¹ • Λ)
    rw [hcan] at c1 c2
    have hA : Adapt F (G i) 𝔡 N' := by
      refine ⟨b2.trans h₀.1, fun a => ?_, fun a => ?_⟩
      · rw [(b1 a).1, (hσe i hi a).1]; exact a1.2.1 a
      · rw [(b1 a).2, (hσe i hi a).2]; exact a1.2.2 a
    refine ⟨c1 ▸ ((WeightInf.main K V H hK r).2 F (G i) 𝔡 Λ).2.1 N' hA, c2.1 ?_⟩
    have haa : N'.aa = (N i).aa := by
      funext a; simp only [NF.aa, hA.1, a1.1]
    rw [((adapt_invariants K V H hK r F (G i) 𝔡 N' hA).2.2.2.2.2.2.2.2 g Λ).1, haa]
    exact ((adapt_invariants K V H hK r F (G i) 𝔡 (N i) a1).2.2.2.2.2.2.2.2 g Λ).1.1 a2
  refine (Finset.sum_le_sum fun i hi => (hmove i hi).1).trans ?_
  rw [← finrank_wt hK he h₀]
  refine GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le K V H hK r N₀ g Λ ι s (fun i => (σ i)⁻¹ • Λ) hg ht₀ (fun i hi => ?_) ?_
  · obtain ⟨a1, -, -, -, -, -, a2⟩ := hN i hi
    have hc : Carr (1 * (σ i * 1)) G₀ (G i) :=
      ((carr_of_sameGr (AdaptInv.sameGr_symm h₀.2.2)).trans (carr_of_eq fun a => (hσe i hi a).2)).trans
        (carr_of_sameGr a1.2.2)
    rw [one_mul, mul_one] at hc
    obtain ⟨d1, d2⟩ := GlobalTheory.T.embeddedDatum_invariant_under_unipotent K V W H HW e hK r F G₀ (G i) 𝔡 N₀ g he h₀
    obtain ⟨e1, -, e2⟩ := d1 (σ i) ((σ i)⁻¹ • Λ) (hσ i hi) hc
    rw [hcan] at e1 e2
    obtain ⟨f1, f2⟩ := d2 ((σ i)⁻¹ • Λ) Λ (e1.symm.trans a2)
    refine ⟨(hmove i hi).2, ?_, ?_, ?_⟩
    · rw [AdaptInv.latL_eq h₀.2.1 h₀.2.2, AdaptInv.latL_eq h₀.2.1 h₀.2.2, e2]
    · rw [AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, f1]
    · rw [AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, f2]
  · rintro i hi i' hi' ⟨ρ, hρ, hρe⟩
    obtain ⟨r1, r2⟩ := (GlobalTheory.UnipStab.mem_R N₀ ρ).1 hρ
    refine hinj i hi i' hi' ⟨σ i' * (ρ * (σ i)⁻¹), GlobalTheory.UnipStab.inN_mul (hσ i' hi') (GlobalTheory.UnipStab.inN_mul
      (AdaptInv.inN_of (AdaptInv.sameGr_symm h₀.2.1) _ r1) (GlobalTheory.UnipStab.inN_inv (hσ i hi))), ?_, ?_⟩
    · rw [mul_smul, mul_smul]
      exact (congrArg (fun L => σ i' • L) hρe).trans (hcan i')
    · have hc : Carr (1 * (σ i' * (ρ * ((σ i)⁻¹ * 1)))) (G i) (G i') :=
        ((((carr_of_sameGr (AdaptInv.sameGr_symm (hN i hi).1.2.2)).trans
          (carr_inv_of_eq fun a => (hσe i hi a).2)).trans (carr_of_inN r2)).trans
          (carr_of_eq fun a => (hσe i' hi' a).2)).trans (carr_of_sameGr (hN i' hi').1.2.2)
      rw [one_mul, mul_one] at hc
      exact hc
end Main

section Count
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def sqM (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) : Matrix (Fin j) (Fin j) K :=
  fun a b => H.B (N.F.e (Fin.castLE hj a)) (N.F'.e (Fin.castLE hj b))

theorem sqM_shape (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) (h : N.j = j) :
    ∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, sqM N j hj a b = w.mat a b * ((sgn b : ℤ) : K) := by
  subst h
  exact ⟨N.w, N.sgn, N.pair⟩

theorem pairM_eq {N N' : NF H r} {j : ℕ} {hj : j ≤ r + 1} (h : sqM N j hj = sqM N' j hj) :
    pairM N.F N.F' j = pairM N'.F N'.F' j := by
  funext a b
  unfold pairM
  split_ifs with hab
  · exact congrFun (congrFun h ⟨a.val, hab.1⟩) ⟨b.val, hab.2⟩
  · rfl

end Count

end GlobalTheory.DegAsm.PerDat

namespace GlobalTheory.DegAsm
open PerDat

theorem sum_weights_per_datum : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (g j T x : ℕ) (δ : ℕ → K) (Λ : Submodule (𝓞 K) V) (d : Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W)) (Del Db : ℝ) (ι : Type) (s : Finset ι) (G : ι → FlagD H r), 1 ≤ g → 1 ≤ x → 1 ≤ Del → 1 ≤ Db → IsEmb F HW e → (∀ i ∈ s, ∃ N : NF H r, Adapt F (G i) 𝔡 N ∧ N.IsTerm g Λ ∧ N.j = j ∧ N.T = T ∧ N.Del = Del ∧ N.Db = Db ∧ N.gI g Λ = x) → (∀ i ∈ s, lab F (G i) j = δ ∧ datOf F (G i) e g Λ = d) → (∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') → ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ datBd K (Module.finrank K W) r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F 𝔡 g j T x δ Λ d Del Db ι s G hg hx hDel hDb he hN hd hinj
  have hDel0 : 0 < Del := by linarith
  have hDb0 : 0 < Db := by linarith
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₁, hi₁⟩
  · rw [Finset.sum_empty]; unfold datBd; positivity
  haveI : Nonempty (NF H r) := ⟨(hN i₁ hi₁).choose⟩
  choose! N hA ht hj hT hD hB hI using hN
  have hjr : j ≤ r := hj i₁ hi₁ ▸ (N i₁).j_le
  have hjr' : j ≤ r + 1 := by omega
  have c1 : ((s.image fun i => sqM (N i) j hjr').card : ℝ) ≤ 8 ^ r := by
    have h1 := GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le K j δ
    have h2 := (Set.encard_le_encard (s := ((s.image fun i => sqM (N i) j hjr' : Finset _) : Set _)) ?_).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard] at h2
      have h3 : (s.image fun i => sqM (N i) j hjr').card ≤ 8 ^ j := by exact_mod_cast h2
      have h4 : 8 ^ j ≤ 8 ^ r := Nat.pow_le_pow_right (by norm_num) hjr
      exact_mod_cast h3.trans h4
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hP)
      refine ⟨sqM_shape _ _ _ (hj i hi), fun l hl => ?_⟩
      have hl' : l ≤ r + 1 := by omega
      rw [← (hd i hi).1, lab, dite_eq_left ⟨hl, hl'⟩, ← AdaptInv.dl_eq (hA i hi).2.1 (hA i hi).2.2]
      rfl
  have c2 : ((s.image fun i => (N i).c).card : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K)) := by
    have h1 := GlobalTheory.DegCnt.NormOneCount.main K hK Del hDel
    have h2 := (ENat.toENNReal_le.2
      (Set.encard_le_encard (s := ((s.image fun i => (N i).c : Finset _) : Set _)) ?_)).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
      exact h2
    · intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
      refine ⟨(N i).c_norm, ?_⟩
      rw [← hD i hi]
      exact GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le K V H hK r (N i) g Λ hg (ht i hi)
  have c3 : ((s.image fun i => (sqM (N i) j hjr', (N i).c)).card : ℝ) ≤
      8 ^ r * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K))) := by
    have h1 : (s.image fun i => (sqM (N i) j hjr', (N i).c)).card ≤
        (s.image fun i => sqM (N i) j hjr').card * (s.image fun i => (N i).c).card := by
      rw [← Finset.card_product]
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩
    refine le_trans ?_ (mul_le_mul c1 c2 (by positivity) (by positivity))
    exact_mod_cast h1
  refine (sum_le_of_fibres s _ _ (((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ 2 * ((Del / x) ^ ((Module.finrank K W : ℝ) / 2) *
      Del ^ (cf K + 2) * (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3))) _ (by positivity) c3
      fun i₀ hi₀ => ?_).trans (le_of_eq ?_)
  · have := one_class (HW := HW) (e := e) hK
      (s.filter fun i => (sqM (N i) j hjr', (N i).c) = (sqM (N i₀) j hjr', (N i₀).c)) G N (G i₀) (N i₀) hg he
      (hA i₀ hi₀) (ht i₀ hi₀) (fun i hi => ?_)
      fun i hi i' hi' => hinj i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1
    · rw [NF.NT, hT i₀ hi₀, hD i₀ hi₀, hB i₀ hi₀, hI i₀ hi₀] at this
      exact this
    · obtain ⟨hi, hk⟩ := Finset.mem_filter.1 hi
      obtain ⟨k1, k2⟩ := Prod.mk.inj hk
      refine ⟨hA i hi, ht i hi, (hj i₀ hi₀).trans (hj i hi).symm, k2.symm, (hT i₀ hi₀).trans (hT i hi).symm, ?_,
        (hd i hi).2.trans (hd i₀ hi₀).2.symm⟩
      rw [hj i₀ hi₀, hj i hi]
      exact pairM_eq k1.symm
  · unfold datBd
    rw [show 3 * cf K + 6 = 2 * (2 + cf K) + (cf K + 2) by ring, Real.rpow_add hDel0 (2 * (2 + cf K))]
    generalize (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3) = y
    generalize Del ^ (2 * (2 + cf K)) = y₁
    generalize Del ^ (cf K + 2) = y₂
    generalize (Del / x) ^ ((Module.finrank K W : ℝ) / 2) = y₃
    ring

end GlobalTheory.DegAsm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFrameClassWeightsLeDatumBound

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_clsOm_le_datBd : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  intro D large₂ X Y u hStd W HW he Λ j x δ d N A hA hT
  obtain ⟨hK, -, -, -, hf, -, -, -, -, -, hV, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hgS : 1 ≤ gS D := by omega
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨-, -, hj0, hδ0, hAd0, hTm0, hg0, -⟩ := hT t₀ ht₀
  obtain ⟨-, -, hLDel, hLDb, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t₀ (N t₀) hAd0
  obtain ⟨-, hx1, -, -, hfW⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t₀)
    (dI D) (N t₀) (gS D) Λ hgS he hAd0 hTm0
  obtain ⟨-, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS (N t₀) (gS D) Λ hgS hTm0
  rw [hg0] at hx1
  rw [hLDel, hj0, hδ0] at hDel1
  rw [hLDb, hj0, hδ0] at hDb1
  let G : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) → Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := fun b =>
    if hb : ∃ t ∈ A, frCls Λ t = b then Ft hb.choose else F0 X u
  have hGb : ∀ b ∈ A.image (frCls Λ), ∃ t ∈ A, frCls Λ t = b ∧ G b = Ft t := by
    intro b hb
    have hb' : ∃ t ∈ A, frCls Λ t = b := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hb'.choose_spec
    exact ⟨hb'.choose, h1, h2, by simp only [G, dif_pos hb']⟩
  have key := GlobalTheory.DegAsm.sum_weights_per_datum D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (dI D)
    (gS D) j (Tu D u) x (fun l => star (δ l)) Λ d (k2Del D j δ) (DbL D j δ) (Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS))
    (A.image (frCls Λ)) G hgS hx1 hDel1 hDb1 he ?_ ?_ ?_
  · have hsum : ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b =
        ∑ b ∈ A.image (frCls Λ), GlobalTheory.DegAsm.omI (F0 X u) (G b) (dI D) Λ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨t, ht, hbt, hG⟩ := hGb b hb
      obtain ⟨-, hlt, -⟩ := hT t ht
      rw [hG, ← hbt, clsOm_frCls hK Λ t hlt]
      unfold omT
      rw [hlt]
    rw [hsum]
    refine key.trans (le_of_eq ?_)
    rw [show Module.finrank D.host.E W = D.R.k by omega, hf]
    rfl
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, hTmt, hgt, -⟩ := hT t ht
    obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨N t, ?_, hTmt, a1.trans hjt, a2, ?_, ?_, hgt⟩
    · rw [hG]; exact hAdt
    · rw [a3, hjt, hδt]
    · rw [a4, hjt, hδt]
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, -, -, hdt⟩ := hT t ht
    obtain ⟨-, -, -, -, a5⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨?_, ?_⟩
    · rw [hG, ← hjt, a5, hδt]
    · rw [hG]; exact hdt
  · intro b hb b' hb' hE
    obtain ⟨t, -, hbt, hG⟩ := hGb b hb
    obtain ⟨t', -, hbt', hG'⟩ := hGb b' hb'
    rw [hG, hG'] at hE
    rw [← hbt, ← hbt']
    exact (frCls_eq_iff hK Λ t t').2 hE

end GlobalTheory.TypeAsm.PerRow
end
end
