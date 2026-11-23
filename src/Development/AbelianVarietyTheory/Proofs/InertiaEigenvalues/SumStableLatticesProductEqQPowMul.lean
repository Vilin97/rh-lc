module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSqStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLatticesStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSnd

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSndStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by
  first | exact @GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | exact GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | (intros; apply GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClearDenominators

section

@[expose] public section

namespace GlobalTheory.ClearDenominatorsIntegral

open GlobalTheory.UnitLemma

theorem clear_denominators (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h

theorem main : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx

end GlobalTheory.ClearDenominatorsIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSnd

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.LinPair

theorem exists_smul_mem_of_mem_span (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)

end GlobalTheory.UnitLemma.LinPair

open GlobalTheory.UnitLemma.LinPair in
theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : (y, (0 : B₂.A)) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem_of_mem_span K M hy
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← (algebraMap K.O K.E).map_zero]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have hmem : d • y ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      simpa [Submodule.mem_comap] using hdy
    refine (Submodule.smul_mem_iff _ hdE).mp ?_
    rw [algebraMap_smul]
    exact Submodule.subset_span hmem
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSndStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | exact GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | (intros; apply GlobalTheory.UnitLemma.InvAlg.lin_fst_snd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.FibSum

theorem fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := GlobalTheory.T.card_stable_lattices_alt K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq

theorem fibsum : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp

end GlobalTheory.UnitLemma.FibSum
end
end
end
