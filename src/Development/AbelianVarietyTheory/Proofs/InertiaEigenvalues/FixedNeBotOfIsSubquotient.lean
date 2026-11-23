module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubquotientJacquetModuleOfSupercuspidalSupStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Mathlib.Algebra.Module.StablyFree.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetProUnipotentRadicalFixedVectorsLift

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix Topology Filter

namespace GlobalTheory.LocGL.ProRadOnto

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_mk_eq {π : Representation ℂ G V} (hπ : IsAdmissible π) {I N : Subgroup G}
    (ho : IsOpen (I : Set G)) (hc : IsCompact (I : Set G)) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M) (hM₀ : ∀ d ∈ M₀, s d ∈ I)
    (C : Set G) (hfac : ∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c)
    (hcon : ∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, d * t = t * d) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U)
    (y : Jacquet π N) (hy : y ∈ fixed (jacquet π N s hs) M₀) :
    ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  set p := (twKer π N 1).mkQ with hp
  set σ := jacquet π N s hs with hσ
  have hps : ∀ m v, p (π (s m) v) = σ m (p v) := fun _ _ => rfl
  have hpN : ∀ x ∈ N, ∀ v, p (π x v) = p v := fun x hx v =>
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨x, hx⟩, v, by simp⟩)
  obtain ⟨u, rfl⟩ : ∃ u, p u = y := Submodule.mkQ_surjective _ y
  obtain ⟨t, htc, ht⟩ := hcon _ ((ho.inter (hπ.1 u)).mem_nhds ⟨one_mem I, by simp⟩)
  set Y := (fixed π I).map p with hY
  haveI := hπ.2 I ho hc
  have key : ∀ w, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) w = w) → (∀ d ∈ M₀, σ d (p w) = p w) →
      σ t (p w) ∈ Y := by
    intro w h1 h2
    refine IwahoriOnto.exists_fixed_map_eq hπ.1 hc p (π (s t) w) fun g hg => ?_
    obtain ⟨d, hd, x, hx, c, hcC, rfl⟩ := hfac g hg
    have h3 : π c (π (s t) w) = π (s t) w := by
      conv_rhs => rw [← h1 c hcC]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3, hps, hpN x hx, hps,
      ← Module.End.mul_apply, ← map_mul, htc d hd, map_mul, Module.End.mul_apply, h2 d hd]
  have hinj : Function.Injective (σ t) := by
    intro a b hab
    have := congrArg (σ t⁻¹) hab
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hst : ∀ z ∈ Y, σ t z ∈ Y := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ g ∈ I, π g w = w := fun g hg => by simpa using hw ⟨g, hg⟩
    exact key w (fun c hcC => hw' _ (ht c hcC).1) fun d hd => by rw [← hps, hw' _ (hM₀ d hd)]
  have hsurj : Function.Surjective ((σ t).restrict hst) :=
    LinearMap.surjective_of_injective fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  obtain ⟨z, hz⟩ := hsurj ⟨_, key u (fun c hcC => (ht c hcC).2) fun d hd => by simpa using hy ⟨d, hd⟩⟩
  have : (z : Jacquet π N) = p u := hinj (congrArg Subtype.val hz)
  exact this ▸ z.2

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem jMinus_contract (e : (Σ a, m a) ≃ n) : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : Levi k m,
    (∀ d : Levi k m, d * t = t * d) ∧ ∀ c ∈ jMinus k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro U hU
  let r : α → ℕ := fun a => (Finset.univ.filter fun b => b < a).card
  have hr : ∀ a b, b < a → r b < r a := fun a b hab =>
    Finset.card_lt_card ⟨fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.trans hab, fun hs => by simpa using hs (show b ∈ _ by simpa using hab)⟩
  let S : kˣ → Levi k m := fun x a => Units.map (Matrix.scalar (m a)).toMonoidHom (x ^ r a)⁻¹
  let T : kˣ → n → kˣ := fun x i => (x ^ r (blk e i))⁻¹
  have hST : ∀ x, leviEmb k e (S x) = diagT k n (T x) := by
    intro x
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    rw [val_diagT, diagonal_apply]
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      simp [S, T, Matrix.scalar_apply, diagonal_pow, diagonal_apply, inv_pow]
    · rw [leviEmb_apply_ne k e _ h, if_neg fun h' => h (congrArg Sigma.fst (e.injective h'))]
  have hcomm : ∀ x (d : Levi k m), d * S x = S x * d := fun x d => funext fun a => Units.ext
    ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq).symm
  let F : Filter (kˣ × jMinus k e) := (comap (fun x : kˣ => (x : k)) (𝓝 0)) ×ˢ ⊤
  have hent : ∀ (x : kˣ) (c : GL n k) i j, ((diagT k n (T x))⁻¹ * c * diagT k n (T x)).val i j =
      (x : k) ^ r (blk e i) * c.val i j * ((x : k) ^ r (blk e j))⁻¹ := by
    intro x c i j
    rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]
    simp [T]
  have hT : Tendsto (fun p : kˣ × jMinus k e => (diagT k n (T p.1))⁻¹ * p.2.1 * diagT k n (T p.1)) F
      (𝓝 1) := by
    rw [SplitFlip.isEmbedding_val_GL.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_def, hent]
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply, Units.val_one]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h0 : ∀ p : kˣ × jMinus k e, (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := fun p =>
        (mem_parabLower_iff k).1 ((mem_unipRadLower k).1 p.2.2.1).1 a b i j hab
      simp only [h0, mul_zero, zero_mul, IwahoriFactor.one_ne e hab.ne]
      exact tendsto_const_nhds
    · have h1 : ∀ p : kˣ × jMinus k e, (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) *
          ((p.1 : k) ^ r a)⁻¹ = (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) := fun p => by
        rw [((mem_unipRadLower k).1 p.2.2.1).2 a i j, IwahoriFactor.one_same, mul_comm, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ p.1.ne_zero), one_mul]
      simp only [h1]
      exact tendsto_const_nhds
    · rw [IwahoriFactor.one_ne e hab.ne', (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
      intro γ _
      have h1 : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ h => h⟩
      have h2 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ h => h⟩
      filter_upwards [prod_mem_prod (preimage_mem_comap (inter_mem h1 h2)) univ_mem] with p hp
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt (hr a b hab)
      have hint : valuation k ((p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) ≤ 1 := by
        have := StepData.mem_KOne.1 p.2.2.2 (e ⟨a, i⟩) (e ⟨b, j⟩)
        rw [Matrix.sub_apply, IwahoriFactor.one_ne e hab.ne', sub_zero] at this
        exact this.le
      have : (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) * ((p.1 : k) ^ r b)⁻¹ =
          p.1 * (p.1 ^ l * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) := by
        rw [hl]; field_simp; ring
      show valuation k _ < _
      rw [this, map_mul, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (mul_le_one' (pow_le_one' hp.1.2.le _) hint)).trans_lt hp.1.1
  haveI : (comap (fun x : kˣ => (x : k)) (𝓝 0)).NeBot := by
    refine comap_neBot fun s hs => ?_
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ValueGroupWithZero k, δ ≠ 0 ∧ δ < γ :=
      ⟨uniformizer k * γ, by simp, mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one⟩
    obtain ⟨x, rfl⟩ := valuation_surjective δ
    exact ⟨Units.mk0 x (by simpa using hδ0), hγ hδ⟩
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (mem_prod_top.1 (hT hU))
  exact ⟨S x, hcomm x, fun c hc => by rw [hST]; exact hx ⟨c, hc⟩⟩

end Local

end GlobalTheory.LocGL.ProRadOnto


open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel in
theorem GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π → ∀ y : Jacquet π (unipRad k e), y ∈ fixed (jacU e π) (leviKOne k m) → ∃ v ∈ fixed π (proRad k e), (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = y := by
  intro k _ _ _ _ α n _ _ m _ _ _ _ e V _ _ π hπ y hy
  obtain ⟨v, hv, h⟩ := ProRadOnto.exists_fixed_mk_eq hπ (isOpen_levelPre _) (isCompact_levelPre _) (leviEmb k e)
    (N := unipRad k e) (leviEmb_mem_normalizer k e) (leviKOne k m)
    (fun d hd => jLevi_le_proRad e ⟨d, hd, rfl⟩) (jMinus k e) (fun g hg => by
      obtain ⟨d, ⟨d', hd', hd⟩, u, hu, c, hc, h⟩ := IwahoriFactor.levi_plus_minus e hg
      exact ⟨d', hd', u, hu.1, c, hc, h.trans (by rw [hd])⟩)
    (fun U hU => by
      obtain ⟨t, ht, h⟩ := ProRadOnto.jMinus_contract e U hU
      exact ⟨t, fun d _ => ht d, h⟩) y hy
  exact ⟨v, hv, h⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetProUnipotentRadicalFixedVectorsLiftStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.jacquet_proUnipotentRadical_fixed_vectors_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π → ∀ y : Jacquet π (unipRad k e), y ∈ fixed (jacU e π) (leviKOne k m) → ∃ v ∈ fixed π (proRad k e), (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = y := by
  first | exact @GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq | exact GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq | (intros; apply GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.DepthZeroPass

theorem fixed_ne_bot_of_isSubquotient {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (hρ : IsSmooth ρ) (h : IsSubquotient τ ρ)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (hτ : fixed τ H ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hτ
  obtain ⟨u, rfl⟩ := hf w
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : V) = v} := by
      ext g
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  obtain ⟨v, hv, hfv⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun g hg => by
    have h1 := mem_fixed.1 hw g hg
    show f (S.toRepresentation g u) = f u
    exact (f.isIntertwining _ _ g u).trans h1
  refine (Submodule.ne_bot_iff _).2 ⟨(v : V), mem_fixed.2 fun g hg => ?_, ?_⟩
  · have := mem_fixed.1 hv g hg
    exact congrArg Subtype.val this
  · intro h0
    apply hw0
    have hv0 : v = 0 := Subtype.ext h0
    have hfv' : f v = f u := hfv
    rw [← hfv', hv0, map_zero]

theorem fixed_piTensor_ne_bot {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (H : ∀ a, Subgroup (Γ a)) (h : ∀ a, fixed (ρ a) (H a) ≠ ⊥) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ H) ≠ ⊥ := by
  choose v hv hv0 using fun a => (Submodule.ne_bot_iff _).1 (h a)
  choose l hl using fun a => Module.Projective.exists_dual_eq_one ℂ (hv0 a)
  refine (Submodule.ne_bot_iff _).2 ⟨PiTensorProduct.tprod ℂ v, mem_fixed.2 fun g hg => ?_, fun h0 => ?_⟩
  · rw [piTensor_tprod]
    congr 1
    funext a
    exact mem_fixed.1 (hv a) (g a) (hg a trivial)
  · have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
    simp [hl] at this

theorem isCompact_leviKOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] :
    IsCompact (leviKOne k m : Set (Levi k m)) := by
  rw [leviKOne, Subgroup.coe_pi]
  exact isCompact_univ_pi fun a => levelPre_bot (k := k) (n := m a) ▸ isCompact_levelPre ⊥

theorem depthZeroInduction : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInduction := by
  intro hG hBZ hZ k _ _ _ _ _ x s hs hfix
  obtain ⟨r, u, e, hu, hsq⟩ := GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport hG hBZ hZ k x s hs
  have hxs : IsSmooth x.rep := x.2.rep.smooth
  have h1 : fixed (piTensor fun a => (u a).rep) (leviKOne k fun a => Fin (u a).1) ≠ ⊥ :=
    fixed_piTensor_ne_bot _ _ fun a => hfix _ (hu a)
  have h2 := fixed_ne_bot_of_isSubquotient (isSmooth_jac e hxs) hsq isCompact_leviKOne h1
  obtain ⟨y, hy1, hy0⟩ := (Submodule.ne_bot_iff _).1 h2
  have hy2 : y ∈ fixed (jacU e x.rep) (leviKOne k fun a => Fin (u a).1) := mem_fixed.2 fun g hg => by
    have h3 := mem_fixed.1 hy1 g hg
    have h4 : deltaHalf k (fun a => Fin (u a).1) g = 1 :=
      deltaHalf_of_mem_leviK fun a _ => StepData.KOne_le_KO (hg a trivial)
    simpa [jac, twist_apply, h4] using h3
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.T.jacquet_proUnipotentRadical_fixed_vectors_lift k e x.rep ((hBZ k).1 _ _ x.rep hxs x.2.rep.irr) y hy2
  refine (Submodule.ne_bot_iff _).2 ⟨v, mem_fixed.2 fun g hg => mem_fixed.1 hv g (KOne_le_proRad e hg), ?_⟩
  rintro rfl
  exact hy0 rfl

end GlobalTheory.DepthZeroPass

end
end
end
