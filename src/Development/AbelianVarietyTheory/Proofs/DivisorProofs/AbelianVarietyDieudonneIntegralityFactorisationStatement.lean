module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithfulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvarietyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegreeStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonneColength_eq_log_degree : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  first | exact @GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | exact GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOfDegNeZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerInv

variable {K : Type} [Field K]

theorem eq_one_of_coprime {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) (m : ℕ) (hm : 0 < m)
    (hcop : Nat.Coprime m (deg f)) {T : Over (Sp K)} (x : T ⟶ A.X)
    (hx : x ≫ f.hom = 1) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨C, q, i, hq, hi, hqi⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A (prod B A) (prodLift f ((m : ℤ) • 𝟙 A))
  have h1 : q ≫ (i ≫ prodFst B A) = f := by
    rw [← Category.assoc, hqi]
    apply Subtype.ext
    change (prodLift f ((m : ℤ) • 𝟙 A)).hom ≫ (prodFst B A).hom = f.hom
    exact lift_fst _ _
  have h2 : q ≫ (i ≫ prodSnd B A) = (m : ℤ) • 𝟙 A := by
    rw [← Category.assoc, hqi]
    apply Subtype.ext
    change (prodLift f ((m : ℤ) • 𝟙 A)).hom ≫ (prodSnd B A).hom = ((m : ℤ) • 𝟙 A).hom
    exact lift_snd _ _
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hqfin : IsFinite q.hom.left := by
    rw [isFinite_iff_finite_ker]
    refine Finite.of_injective (β := (ptMap f).ker)
      (fun y => ⟨y.1, ?_⟩) (by intro y z h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    have hy : y.1 ≫ q.hom = 1 := y.2
    rw [MonoidHom.mem_ker, ptMap_apply, ← h1, comp_hom, ← Category.assoc, hy, one_comp]
  have hAC : A.dim = C.dim := le_antisymm ((DimLe.dim_le K A C q).1 hqfin) ((DimLe.dim_le K A C q).2 hq)
  have hAB : A.dim = B.dim := (isogeny_flat_finrank K A B f hf).1
  have hd1 := (isIsogeny_comp_iff_and_deg_comp K A C B q (i ≫ prodFst B A) hAC (hAC ▸ hAB)).2
  rw [h1] at hd1
  have hd2 := (isIsogeny_comp_iff_and_deg_comp K A C A q (i ≫ prodSnd B A) hAC hAC.symm).2
  rw [h2, (MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')).2, Int.natAbs_natCast] at hd2
  have hq1 : deg q = 1 := by
    have a : deg q ∣ deg f := ⟨_, hd1⟩
    have b : deg q ∣ m ^ (2 * A.dim) := ⟨_, hd2⟩
    exact Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left _ hcop).coprime_dvd_left b) a
  have hiso : IsIso q := (isIso_iff_deg_eq_one K A C q).2 hq1

  have hy1 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = 1 := by
    have := congrArg Hom.hom h1
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this]
    exact hx
  have hy2 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = 1 := by
    have := congrArg Hom.hom h2
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this, zsmul_hom, id_hom, zpow_natCast, MonObj.comp_pow,
      Category.comp_id, hxm]
  have hyi : (x ≫ q.hom) ≫ i.hom = (1 : T ⟶ C.X) ≫ i.hom := by
    rw [MonObj.one_comp]
    apply CartesianMonoidalCategory.hom_ext
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodFst B A).hom
      rw [hy1, MonObj.one_comp]
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodSnd B A).hom
      rw [hy2, MonObj.one_comp]
  have hmono : Mono i.hom.left := inferInstance
  have hy : x ≫ q.hom = 1 := by
    apply Over.OverMorphism.ext
    have := congrArg Over.Hom.left hyi
    simp only [Over.comp_left] at this
    exact (cancel_mono i.hom.left).1 this
  have hqq : q.hom ≫ (inv q).hom = 𝟙 A.X := by
    rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  calc x = (x ≫ q.hom) ≫ (inv q).hom := by rw [Category.assoc, hqq, Category.comp_id]
    _ = 1 := by rw [hy, MonObj.one_comp]

theorem kernel_killed_of_deg_ne_zero (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f)
    (hd : ((deg f : ℕ) : K) ≠ 0) :
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  obtain ⟨n0, hn0, hkill⟩ := KerKill.kernel_killed K A B f hf.1
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hpp.ne_one
    refine ⟨M, ?_, ?_⟩
    · rwa [Ne, CharP.cast_eq_zero_iff K p]
    · intro T x hx
      have hpd : ¬ p ∣ deg f := by rwa [Ne, CharP.cast_eq_zero_iff K p] at hd
      refine eq_one_of_coprime f hf (p ^ k) (pow_pos hpp.pos k)
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpd)) (x ^ M) ?_ ?_
      · rw [MonObj.pow_comp, hx, one_pow]
      · rw [← pow_mul, mul_comm]; exact hkill T x hx
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨n0, by exact_mod_cast hn0.ne', hkill⟩

end GlobalTheory.AV.KerInv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (GlobalTheory.T.dieudonne_integrality_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree p k A B G H t t' f hf
  exact ⟨h1, GlobalTheory.T.dieudonneColength_eq_log_degree p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
end
end
