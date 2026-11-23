module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompBaseChange

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem eigen_decomp_base_change :
  ∀ (K C : Type) [CommRing K] [CommRing C] (n a : ℕ) (ω : K) (tr nm : ℤ), ω ^ 2 - (tr : K) * ω + (nm : K) = 0 → ∀ (f : K →+* Matrix (Fin n) (Fin n) C) (ρ : C), ρ ^ 2 - (tr : C) * ρ + (nm : C) = 0 → IsUnit (2 * ρ - (tr : C)) → ∀ (t : Fin a → (K →+* C)), (∀ i, t i ω = ρ) → (∀ v : Fin n → C, Matrix.mulVec (f ω) v = ρ • v → ∃ w : Fin a → Fin n → C, (∀ i (c : K), Matrix.mulVec (f c) (w i) = t i c • w i) ∧ v = ∑ i, w i) → ∀ (R' : Type) [CommRing R'] (g : C →+* R') (v : Fin n → R'), Matrix.mulVec ((f ω).map g) v = g ρ • v → ∃ w : Fin a → Fin n → R', (∀ i (c : K), Matrix.mulVec ((f c).map g) (w i) = g (t i c) • w i) ∧ v = ∑ i, w i := by
  intro K C _ _ n a ω tr nm hω f ρ hρ hu t ht H R' _ g v hv
  obtain ⟨uinv, huinv⟩ : ∃ uinv : C, uinv * (2 * ρ - (tr : C)) = 1 := by
    obtain ⟨u, hu'⟩ := hu
    exact ⟨↑u⁻¹, by rw [← hu']; simp⟩
  set Ω := f ω with hΩdef

  have hΩΩ : Ω * Ω = (tr : Matrix (Fin n) (Fin n) C) * Ω - (nm : Matrix (Fin n) (Fin n) C) := by
    have h1 : ω * ω = (tr : K) * ω - (nm : K) := by linear_combination hω
    have h2 := congrArg f h1
    simpa [map_mul, map_sub, map_intCast] using h2
  have key : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x) = (tr : C) • (Ω *ᵥ x) - (nm : C) • x := by
    intro x
    rw [mulVec_mulVec, hΩΩ, sub_mulVec, ← mulVec_mulVec, intCast_mulVec, intCast_mulVec]
  have eig : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x - ((tr : C) - ρ) • x) = ρ • (Ω *ᵥ x - ((tr : C) - ρ) • x) := by
    intro x
    rw [mulVec_sub, mulVec_smul, key]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(x k)) * hρ
  let e : Fin n → Fin n → C := fun j => uinv • (Ω *ᵥ Pi.single j 1 - ((tr : C) - ρ) • Pi.single j 1)
  have he : ∀ j, Ω *ᵥ e j = ρ • e j := by
    intro j
    simp only [e, mulVec_smul, eig]
    rw [smul_comm]
  choose W hW hWsum using fun j => H (e j) (he j)

  have hmap : ∀ (M : Matrix (Fin n) (Fin n) C) (x : Fin n → C), M.map g *ᵥ (g ∘ x) = g ∘ (M *ᵥ x) := by
    intro M x
    funext k
    simp only [Function.comp_apply]
    rw [RingHom.map_mulVec]
  have hvsum : v = ∑ j, v j • (g ∘ e j) := by
    funext k
    have hv' := congrFun hv k
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hv'
    simp only [e, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.sub_apply,
      mulVec_single_one, col_apply, Pi.single_apply, map_mul, map_sub, mul_ite, mul_one, mul_zero,
      map_zero]
    have hterm : ∀ x, v x * (g uinv * (g (Ω k x) - g (if k = x then (tr : C) - ρ else 0))) =
        g uinv * (g (Ω k x) * v x) - (if k = x then g uinv * g ((tr : C) - ρ) * v k else 0) := by
      intro x
      split_ifs with h
      · subst h; ring
      · simp only [map_zero, sub_zero]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum, hv',
      Finset.sum_ite_eq]
    have hg := congrArg g huinv
    simp only [map_mul, map_sub, map_intCast, map_one, map_ofNat] at hg ⊢
    simp only [Finset.mem_univ, if_true]
    linear_combination (-(v k)) * hg
  refine ⟨fun i => ∑ j, v j • (g ∘ W j i), ?_, ?_⟩
  · intro i c
    rw [mulVec_sum]
    simp only [mulVec_smul, hmap, hW]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    congr 1
    funext k
    simp [Function.comp_apply]
  · conv_lhs => rw [hvsum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    rw [hWsum j]
    funext k

    simp [Finset.sum_apply, map_sum]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieSpreadFromIdentityPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieSpread

theorem prod_ofFn_eq {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq T h0 hadd (fun i => w i.succ)]

theorem mat_ext {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem isUnit_two_rho_sub {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hsq : (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
    have := b.ρ_root; push_cast; linear_combination 4 * this
  have hd : D.tr ^ 2 - 4 * D.nm = -(((D.tr ^ 2 - 4 * D.nm).natAbs : ℕ) : ℤ) := by
    have := D.disc_neg; omega
  have hcop : ((D.tr ^ 2 - 4 * D.nm).natAbs).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h; exact D.disc_p (Int.natCast_dvd.mpr h)
  have hu := b.unit _ hcop
  rw [← isUnit_pow_iff (n := 2) two_ne_zero, hsq, hd]
  rw [Int.cast_neg, Int.cast_natCast]
  exact hu.neg

def TangentCoordinatesSmoothCommGroupLocalRing : Prop :=
  ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'),
      ∃ T : (Fin n → R') → (GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G), Function.Injective T ∧
        (∀ v : GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
          (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧
        (∀ c c', T (c + c') = T c * T c') ∧
        (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧
        ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)

theorem spread_of_coord (hcoord : TangentCoordinatesSmoothCommGroupLocalRing) : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  intro p _ D R _ b C _ _ tR A _ _ hsm act hlie R' _ β x hx
  obtain ⟨g0, rfl⟩ : ∃ g0 : C →+* R', spMap g0 = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hg : g0.comp tR = β := by
    have h1 : Spec.map (CommRingCat.ofHom (g0.comp tR)) = Spec.map (CommRingCat.ofHom β) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]; exact hx
    have h2 := Spec.map_injective h1
    simpa using congrArg CommRingCat.Hom.hom h2
  have hgapp : ∀ r, g0 (tR r) = β r := fun r => by rw [← hg]; rfl
  obtain ⟨n, M, hM⟩ := hcoord C A hsm
  obtain ⟨T1, T1inj, T1rng, T1add, T1sm, T1u⟩ := hM C (RingHom.id C)
  obtain ⟨T0, T0inj, T0rng, T0add, T0sm, T0u⟩ := hM R' g0
  have T1zero : T1 0 = 1 := by
    have h := T1add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have T0zero : T0 0 = 1 := by
    have h := T0add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hid : ∀ u : A ⟶ A, (M u).map (RingHom.id C) = M u := fun u => by ext; simp
  let fa : 𝓞 D.F → Matrix (Fin n) (Fin n) C := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have key : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((fa c).mulVec v) := fun c v => by
    rw [T1u _ (act.hom _) v, hid]
  have f1 : fa 1 = 1 := mat_ext fun v => T1inj (by
    rw [← key, map_one, act.one, Category.comp_id, Matrix.one_mulVec])
  have fmul : ∀ c d, fa (c * d) = fa c * fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_mul, act.mul, ← Category.assoc, key, key, Matrix.mulVec_mulVec])
  have fadd : ∀ c d, fa (c + d) = fa c + fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_add (f := _), act.add, MonObj.comp_mul, key, key, ← T1add, Matrix.add_mulVec])
  have f0 : fa 0 = 0 := by
    have h := fadd 0 0; rw [add_zero] at h; exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : 𝓞 D.F →+* Matrix (Fin n) (Fin n) C :=
    { toFun := fa, map_one' := f1, map_mul' := fmul, map_zero' := f0, map_add' := fadd }
  have keyf : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((f c).mulVec v) := key
  have keyg : ∀ (c : 𝓞 D.F) u, T0 u ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T0 (((f c).map g0).mulVec u) :=
    fun c u => T0u _ (act.hom _) u
  have hω : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : (tR b.ρ) ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root; simpa using this
  have hunit : IsUnit (2 * tR b.ρ - (D.tr : C)) := by
    simpa [map_ofNat] using (isUnit_two_rho_sub b).map tR
  let t : Fin D.a → (𝓞 D.F →+* C) := fun i => tR.comp (b.t i)
  have ht : ∀ i, t i D.ω = tR b.ρ := fun i => by simp [t, b.t_ω]
  have hyp : ∀ v : Fin n → C, (f D.ω).mulVec v = tR b.ρ • v → ∃ w : Fin D.a → Fin n → C,
      (∀ i (c : 𝓞 D.F), (f c).mulVec (w i) = t i c • w i) ∧ v = ∑ i, w i := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hlie (T1 v) ⟨(T1rng _).2 ⟨v, rfl⟩, by rw [keyf, hv]; exact T1sm _ _⟩
    choose w' hw' using fun i => (T1rng (w i)).1 (hw i 0).1
    refine ⟨w', fun i c => T1inj ?_, T1inj ?_⟩
    · rw [← keyf, hw' i]
      apply Over.OverMorphism.ext
      rw [T1sm, hw' i]
      exact (hw i c).2
    · rw [hvw, ← prod_ofFn_eq T1 T1zero T1add]
      simp only [hw']
  have L := GlobalTheory.eigen_decomp_base_change (𝓞 D.F) C n D.a D.ω D.tr D.nm hω f (tR b.ρ) hρ hunit t ht hyp R' g0
  intro v hv
  obtain ⟨v', rfl⟩ := (T0rng v).1 hv.1
  obtain ⟨w, hw, hvw⟩ := L v' (T0inj (by
    apply Over.OverMorphism.ext
    rw [← keyg, T0sm, hgapp]
    exact hv.2))
  refine ⟨fun i => T0 (w i), fun i c => ⟨(T0rng _).2 ⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [keyg, hw i c, T0sm]
    rw [show g0 (t i c) = β (b.t i c) from hgapp _]
  · rw [hvw, prod_ofFn_eq T0 T0zero T0add]

theorem lieAt_spread : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x :=
  spread_of_coord GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group

end GlobalTheory.HTLieSpread
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieSpreadFromIdentityPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylorLie_spread_from_identity_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  first | exact @GlobalTheory.HTLieSpread.lieAt_spread | exact GlobalTheory.HTLieSpread.lieAt_spread | (intros; apply GlobalTheory.HTLieSpread.lieAt_spread <;> assumption)
end
end
