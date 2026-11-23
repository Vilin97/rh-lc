module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalResidueTensorInjective
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaNonemptyEquivOfLocalQuotientMatrixStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelQuotientModuleSurjection

section

@[expose] public section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.level_quotient_module_surjection : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.latQuot_free) | (exact GlobalTheory.UPel.HT.EtLev.latQuot_free) | (intros; apply GlobalTheory.UPel.HT.EtLev.latQuot_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderSurjectsMatrixAlgebraModPrimePower

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.MatRed

theorem approx {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ) (x : M ⊗[ℤ] ℤ_[p]) :
    ∃ (b : M) (y : M ⊗[ℤ] ℤ_[p]), x = b ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul o z =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec r z)
    refine ⟨(z.appr r) • o, o ⊗ₜ w, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    congr 1
    rw [nsmul_eq_mul, nsmul_eq_mul, _root_.mul_one]
    push_cast
    linear_combination hw
  | add x y hx hy =>
    obtain ⟨a, u, ha⟩ := hx
    obtain ⟨b, v, hb⟩ := hy
    exact ⟨a + b, u + v, by rw [ha, hb, TensorProduct.add_tmul, smul_add]; abel⟩

theorem dvd_of_tmul {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (r : ℕ) (u : M) (z : M ⊗[ℤ] ℤ_[p]) (h : u ⊗ₜ (1 : ℤ_[p]) = (p ^ r) • z) :
    ∃ v : M, u = (p ^ r) • v := by
  let bs := Module.Free.chooseBasis ℤ M
  have hd : ∀ i, ((p ^ r : ℕ) : ℤ) ∣ bs.repr u i := by
    intro i
    let φ : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p] :=
      (TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (bs.coord i) LinearMap.id
    have h1 : φ (u ⊗ₜ (1 : ℤ_[p])) = ((bs.repr u i : ℤ) : ℤ_[p]) := by
      show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (bs.coord i) LinearMap.id (u ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
      simp [zsmul_eq_mul]
    rw [h, map_nsmul] at h1
    have h2 := congrArg (PadicInt.toZModPow (p := p) r) h1
    rw [map_nsmul, map_intCast] at h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2, nsmul_eq_mul]
    simp
  choose k hk using hd
  refine ⟨∑ i, k i • bs i, ?_⟩
  conv_lhs => rw [← bs.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk i, mul_smul, natCast_zsmul]

theorem mem_smul_top_map {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (f : X →ₗ[R] Y) {x : X} (hx : x ∈ I • (⊤ : Submodule R X)) :
    f x ∈ I • (⊤ : Submodule R Y) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem exists_matRed : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  intro p _ D w0 r _ hp
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e⟩ := D.splitP
  have hpr : (p : 𝓞 D.F) ^ r ∈ w0 ^ r := Ideal.pow_mem_pow hp r
  have hA : ((p ^ r : ℕ) : 𝓞 D.F ⧸ w0 ^ r) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hpr
    simpa using h
  let ψ₀ : ℤ_[p] →+* 𝓞 D.F ⧸ w0 ^ r :=
    (ZMod.castHom (ringChar.dvd hA) (𝓞 D.F ⧸ w0 ^ r)).comp (PadicInt.toZModPow r)
  let ψ : 𝓞 D.F ⊗[ℤ] ℤ_[p] →ₐ[𝓞 D.F] 𝓞 D.F ⧸ w0 ^ r :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (𝓞 D.F) (w0 ^ r)) ψ₀.toIntAlgHom
      (fun _ _ => Commute.all _ _)
  have hψ : ∀ c, ψ (c ⊗ₜ (1 : ℤ_[p])) = Ideal.Quotient.mk _ c := by
    intro c; simp [ψ, Algebra.TensorProduct.lift_tmul]
  have hψk : ∀ y, ψ y = 0 → y ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    intro y hy
    obtain ⟨c, z, rfl⟩ := approx r y
    rw [map_add (f := _), map_nsmul, hψ, nsmul_eq_mul, hA, zero_mul, add_zero] at hy
    have hc : c ∈ w0 ^ r := Ideal.Quotient.eq_zero_iff_mem.1 hy
    have h1 : c ⊗ₜ[ℤ] (1 : ℤ_[p]) = c • (1 : 𝓞 D.F ⊗[ℤ] ℤ_[p]) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (p ^ r) • z = ((p : 𝓞 D.F) ^ r) • z := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc trivial) (Submodule.smul_mem_smul hpr trivial)
  let incl : D.O →ₐ[𝓞 D.F] D.O ⊗[ℤ] ℤ_[p] := Algebra.TensorProduct.includeLeft
  have hincl : ∀ b, incl b = b ⊗ₜ (1 : ℤ_[p]) := fun b => rfl
  refine ⟨ψ.mapMatrix.comp (e.toAlgHom.comp incl), ?_, ?_⟩
  · intro N
    choose c hc using fun i j => Ideal.Quotient.mk_surjective (N i j)
    obtain ⟨b, y, hby⟩ := approx (M := D.O) r (e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])))
    refine ⟨b, ?_⟩
    have hb : incl b = e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])) - (p ^ r) • y := by
      rw [hby, hincl]; abel
    show ψ.mapMatrix (e (incl b)) = N
    rw [hb, map_sub, map_sub, map_nsmul, map_nsmul, e.apply_symm_apply]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, nsmul_eq_mul, hA, zero_mul, sub_zero]
    simp [AlgHom.mapMatrix_apply, hψ, hc]
  · intro b hb
    have hb' : ∀ i j, ψ (e (incl b) i j) = 0 := fun i j => by
      have h := congrFun (congrFun hb i) j
      simpa [AlgHom.mapMatrix_apply] using h
    have hM : e (incl b) ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]))) := by
      rw [Matrix.matrix_eq_sum_single (e (incl b))]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      exact mem_smul_top_map _ (Matrix.singleLinearMap (𝓞 D.F) i j) (hψk _ (hb' i j))
    have hO : incl b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])) := by
      have h := mem_smul_top_map _ e.symm.toLinearEquiv.toLinearMap hM
      simpa using h
    have claim : ∀ x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])),
        ∃ b' ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O), ∃ z : D.O ⊗[ℤ] ℤ_[p],
          x = b' ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • z := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro c hc x _
        obtain ⟨bx, y, rfl⟩ := approx r x
        refine ⟨c • bx, Submodule.smul_mem_smul hc trivial, c • y, ?_⟩
        rw [smul_add, TensorProduct.smul_tmul', smul_comm]
      · rintro x y ⟨a, ha, u, rfl⟩ ⟨a', ha', v, rfl⟩
        exact ⟨a + a', add_mem ha ha', u + v, by rw [TensorProduct.add_tmul, smul_add]; abel⟩
    obtain ⟨b', hb'', z, hz⟩ := claim _ hO
    rw [hincl] at hz
    have h3 : (b - b') ⊗ₜ[ℤ] (1 : ℤ_[p]) = (p ^ r) • z := by
      rw [TensorProduct.sub_tmul, hz]; abel
    obtain ⟨v, hv⟩ := dvd_of_tmul r (b - b') z h3
    have h4 : b = b' + ((p : 𝓞 D.F) ^ r) • v := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hv]; abel
    rw [h4]
    exact add_mem hb'' (Submodule.smul_mem_smul hpr trivial)

end GlobalTheory.UPel.HT.MatRed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderSurjectsMatrixAlgebraModPrimePowerStatement

section

@[expose] public section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.MatRed.exists_matRed) | (exact GlobalTheory.UPel.HT.MatRed.exists_matRed) | (intros; apply GlobalTheory.UPel.HT.MatRed.exists_matRed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.EtLevMorita

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

section Act

variable {O : Type} [Ring O] {G : Type} [CommGroup G] (act : O → G → G)
  (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
  (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)

include hmul in
theorem act_one_eq (b : O) : act b 1 = 1 := by
  have h := hmul b 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.1 h

include hadd in
theorem act_zero_eq (g : G) : act 0 g = 1 := by
  have h := hadd 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.1 h

def actModule : Module O (Additive G) where
  smul b x := Additive.ofMul (act b x.toMul)
  one_smul x := by show Additive.ofMul (act 1 x.toMul) = x; rw [hone]; rfl
  mul_smul b c x := congrArg Additive.ofMul (hcomp b c x.toMul)
  smul_zero b := congrArg Additive.ofMul (act_one_eq act hmul b)
  smul_add b x y := congrArg Additive.ofMul (hmul b x.toMul y.toMul)
  add_smul b c x := congrArg Additive.ofMul (hadd b c x.toMul)
  zero_smul x := congrArg Additive.ofMul (act_zero_eq act hadd x.toMul)

end Act

end GlobalTheory.EtLevMorita


open GlobalTheory.EtLevMorita in
theorem GlobalTheory.EtLevMorita.exists_lev : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  intro p _ D w0 r hw hp G _ act hmul hone hcomp hadd f hfadd hfsm hfinj hfonto
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ => 1, fun _ _ => (_root_.mul_one 1).symm, fun b _ => (act_one_eq act hmul b).symm,
      fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
    · simp only [true_iff]
      have hx : x = algebraMap (𝓞 D.F) D.O 1 • x := by simp
      rw [hx]
      exact Submodule.subset_span ⟨1, by simp, x, rfl⟩
    · have h1 := hg 1 (by simp)
      rw [map_one, hone] at h1
      exact h1.symm
  · haveI := isLocalRing_quot_pow w0 r hr.ne'
    letI : Module D.O (Additive G) := actModule act hmul hone hcomp hadd
    letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    have hsm : ∀ (b : D.O) (x : Additive G), b • x = Additive.ofMul (act b x.toMul) := fun _ _ => rfl
    let T : Submodule D.O (Additive G) :=
      { carrier := {x | ∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) x.toMul = 1}
        add_mem' := fun {x y} hx hy c hc => by
          show act _ (x.toMul * y.toMul) = 1
          rw [hmul, hx c hc, hy c hc, _root_.mul_one]
        zero_mem' := fun c _ => act_one_eq act hmul _
        smul_mem' := fun b x hx c hc => by
          show act _ (act b x.toMul) = 1
          rw [← hcomp, Algebra.commutes, hcomp, hx c hc, act_one_eq act hmul] }
    have hf0 : f 0 = 1 := by
      have h := hfadd 0 0
      rw [add_zero] at h
      exact left_eq_mul.1 h
    have hfT : ∀ a, Additive.ofMul (f a) ∈ T := fun a c hc => by
      show act _ (f a) = 1
      rw [← hfsm, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_smul, hf0]
    let fl : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) →ₗ[𝓞 D.F] T :=
      { toFun := fun a => ⟨Additive.ofMul (f a), hfT a⟩
        map_add' := fun a a' => Subtype.ext (by
          show Additive.ofMul (f (a + a')) = Additive.ofMul (f a) + Additive.ofMul (f a')
          rw [hfadd]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          show Additive.ofMul (f (c • a)) = algebraMap (𝓞 D.F) D.O c • Additive.ofMul (f a)
          rw [← algebraMap_smul (𝓞 D.F ⧸ w0 ^ r) c a, Ideal.Quotient.algebraMap_eq, hfsm]
          rfl) }
    have hfl : Function.Bijective fl := by
      refine ⟨fun a a' h => hfinj (congrArg (fun t : T => (t : Additive G).toMul) h), fun t => ?_⟩
      obtain ⟨a, ha⟩ := hfonto (t : Additive G).toMul t.2
      exact ⟨a, Subtype.ext (by show Additive.ofMul (f a) = _; rw [ha]; rfl)⟩
    let eT : T ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) := (LinearEquiv.ofBijective fl hfl).symm
    obtain ⟨g, hgs, hgsm, hgker⟩ := GlobalTheory.T.level_quotient_module_surjection p D w0 r hw
    let gl : D.La →ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c x => by
          show g (algebraMap (𝓞 D.F) D.O c • x) = c • g x
          rw [hgsm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
    have hker : LinearMap.ker gl = (wSub D w0 r).restrictScalars (𝓞 D.F) := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact hgker x
    let eL : (D.La ⧸ wSub D w0 r) ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      (Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D w0 r)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ gl.quotKerEquivOfSurjective hgs
    obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power p D w0 r hw hp
    obtain ⟨e⟩ := GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix (𝓞 D.F) (w0 ^ r) inferInstance D.m D.n D.m_pos D.O φ hφs hφk
      (D.La ⧸ wSub D w0 r) T eL eT
    refine ⟨fun x => ((e (Submodule.Quotient.mk x) : T) : Additive G).toMul, fun x y => ?_, fun b x => ?_,
      fun x => ?_, fun g hg => ?_⟩
    · simp only [Submodule.Quotient.mk_add, map_add (f := _), Submodule.coe_add, toMul_add]
    · simp only [Submodule.Quotient.mk_smul, map_smul, Submodule.coe_smul, hsm, toMul_ofMul]
    · rw [toMul_eq_one, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm ⟨Additive.ofMul g, hg⟩)
      refine ⟨y, ?_⟩
      simp only [hy, LinearEquiv.apply_symm_apply, toMul_ofMul]
end
end
end
