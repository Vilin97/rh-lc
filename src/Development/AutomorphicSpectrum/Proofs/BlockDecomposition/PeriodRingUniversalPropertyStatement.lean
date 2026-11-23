module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.RingTheory.WittVector.Teichmuller
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Perfection
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PerfectWittMaps

theorem isAdicComplete_of_pow_eq_zero (p : ℕ) {B : Type} [CommRing B] {n : ℕ} (hn : (p : B) ^ n = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hI : (Ideal.span {(p : B)}) ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn]; simp
  have hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y := by
    intro x y h
    rw [hI] at h
    simpa [SModEq.bot] using h
  refine { haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hmn
  · exact h hmn
  · rw [hz0 _ _ (h hmn)]

theorem exists_pow_pow_eq (p : ℕ) {A : Type} [CommRing A] (h : Function.Bijective fun x : A => x ^ p)
    (k : ℕ) (a : A) : ∃ b : A, b ^ p ^ k = a := by
  induction k generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h.2 a
    obtain ⟨b, hb⟩ := ih c
    refine ⟨b, ?_⟩
    rw [pow_succ, pow_mul, hb]
    exact hc

theorem exists_lift (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] [IsAdicComplete (Ideal.span {(p : B)}) B] (J : Ideal B)
    (hpJ : (p : B) ∈ J) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) (g : A →+* B ⧸ J) :
    ∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a := by
  let φ : B ⧸ J →+* ModP B p := Ideal.Quotient.lift J
    ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by
      intro x hx
      rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ x hx)
  let σ : A →+* A := ((frobeniusEquiv A p).symm : A ≃+* A)
  let g₁ : A →+* ModP B p := φ.comp (g.comp σ)
  let G : A →+* PreTilt B p := Perfection.lift p A (ModP B p) g₁
  have hle : Ideal.span {(p : B)} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hpJ
  let res : ModP B p →+* B ⧸ J := Ideal.Quotient.factor hle
  have hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u) := fun u => rfl
  have hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p) := by
      simp [φ, frobenius_def]
    rw [this, ← hres, map_pow]
  refine ⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩
  have h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a)
      = (G a).untilt := by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
  have h3 : PreTilt.coeff 0 (G a) = g₁ a := rfl
  rw [h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]
  change res (φ (g (σ a))) = g a
  rw [hφ, ← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p A p a

theorem lift_unique (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] (J : Ideal B) (n : ℕ) (hbij : Function.Bijective fun x : A => x ^ p)
    (hn : (p : B) ^ n = 0) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)})
    (f f' : WittVector p A →+* B)
    (h : ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) =
      Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) : f = f' := by
  refine WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_
  obtain ⟨b, rfl⟩ := exists_pow_pow_eq p hbij (n + 1) a
  rw [map_pow, map_pow, map_pow]
  set u := f (WittVector.teichmuller p b)
  set v := f' (WittVector.teichmuller p b)
  have huv : u - v ∈ J := Ideal.Quotient.eq.1 (h b)
  have h1 : (p : B) ∣ u ^ p - v ^ p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow,
      ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ _ huv
  have h2 := dvd_sub_pow_of_dvd_sub h1 n
  have h0 : (p : B) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  exact h2

theorem wittVector_lift : ∀ (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] (J : Ideal B) (n : ℕ), D.Pf p A → (p : B) ^ n = 0 → (p : B) ∈ J → (∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) → ∀ g : A →+* B ⧸ J, (∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a) ∧ ∀ f f' : WittVector p A →+* B, (∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) → f = f' := by
  intro p _ A B _ _ J n hA hn hpJ hJ g
  by_cases hB : Subsingleton B
  · have hQ : Subsingleton (B ⧸ J) := (Ideal.Quotient.mk_surjective (I := J)).subsingleton
    refine ⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
               map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩,
      fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩
  · rw [not_subsingleton_iff_nontrivial] at hB
    have hu : ¬IsUnit (p : B) := IsNilpotent.not_isUnit ⟨n, hn⟩
    haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩
    haveI := isAdicComplete_of_pow_eq_zero p hn
    have hAn : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      have h1 : (1 : B) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]
      have h2 := hJ 1 h1
      rw [one_pow, Ideal.mem_span_singleton] at h2
      exact hu (isUnit_of_dvd_one h2)
    haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char
    haveI : PerfectRing A p := ⟨hA.bij⟩
    exact ⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩

end GlobalTheory.CompanionTheory.PerfectWittMaps
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem pow_mem_map {R B : Type} [CommRing R] [CommRing B] (h : R →+* B) (I : Ideal R) (p : ℕ) (hp : p.Prime)
    (hI : ∀ x ∈ I, x ^ p ∈ Ideal.span {(p : R)}) : ∀ x ∈ I.map h, x ^ p ∈ Ideal.span {(p : B)} := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => x ^ p ∈ Ideal.span {(p : B)}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hI y hy)
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [zero_pow hp.ne_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
    rw [hr]
    exact add_mem (add_mem ha hb) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))))
  · intro a b _ hb
    rw [smul_eq_mul, mul_pow]
    exact Ideal.mul_mem_left _ _ hb

section Tens

variable {R S T C B : Type} [CommRing R] [CommRing S] [CommRing T] [CommRing C] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra R C] [Algebra S C] [Algebra T C]
  [IsScalarTower R S C] [IsScalarTower R T C]


open TensorProduct in
theorem tens_ext
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (f f' : C →+* B) (h1 : ∀ s, f (algebraMap S C s) = f' (algebraMap S C s))
    (h2 : ∀ t, f (algebraMap T C t) = f' (algebraMap T C t)) : f = f' := by
  refine RingHom.ext fun c => ?_
  obtain ⟨z, rfl⟩ := hs c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom',
      map_mul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]


open TensorProduct in
theorem tens_desc (m n : ℕ)
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (hk : ∀ z : S ⊗[R] T, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _) z = 0 ↔
        z ∈ Ideal.span {(m : S ⊗[R] T) ^ n})
    (u : S →+* B) (v : T →+* B) (huv : ∀ r, u (algebraMap R S r) = v (algebraMap R T r))
    (hm : (m : B) ^ n = 0) :
    ∃ f : C →+* B, (∀ s, f (algebraMap S C s) = u s) ∧ ∀ t, f (algebraMap T C t) = v t := by
  letI : Algebra R B := (u.comp (algebraMap R S)).toAlgebra
  let u' : S →ₐ[R] B := { u with commutes' := fun _ => rfl }
  let v' : T →ₐ[R] B := { v with commutes' := fun r => (huv r).symm }
  let L : S ⊗[R] T →ₐ[R] B := Algebra.TensorProduct.lift u' v' (fun _ _ => Commute.all _ _)
  let Φ : S ⊗[R] T →ₐ[R] C := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
    (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)
  have hker : RingHom.ker (Φ : S ⊗[R] T →+* C) ≤ RingHom.ker (L : S ⊗[R] T →+* B) := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((hk z).1 hz)
    rw [RingHom.mem_ker, map_mul, map_pow, map_natCast, hm, mul_zero]
  let f : C →+* B := (Φ : S ⊗[R] T →+* C).liftOfSurjective hs ⟨(L : S ⊗[R] T →+* B), hker⟩
  have hf : ∀ z, f (Φ z) = L z := fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z
  refine ⟨f, fun s => ?_, fun t => ?_⟩
  · have h := hf (s ⊗ₜ 1)
    simpa [Φ, L, u'] using h
  · have h := hf (1 ⊗ₜ t)
    simpa [Φ, L, v'] using h

end Tens

end GlobalTheory.CompanionTheory.AcrUniv

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem maps_out : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  intro l _ A n B _ h
  have hp : l.Prime := Fact.out
  obtain ⟨⟨π, -, -⟩, hFil, -, -, -, -, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  obtain ⟨-, -, -, -, -, hpow, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal (base l) n
  have hlB : (l : B) ^ n = 0 := by
    rw [← map_natCast h, ← map_pow, pow_l_acr, map_zero]
  have hlJ : (l : B) ∈ ((base l).PFil n).map h := by
    rw [← map_natCast h]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hJp : ∀ x ∈ ((base l).PFil n).map h, x ^ l ∈ Ideal.span {(l : B)} :=
    pow_mem_map h _ l hp fun x hx => (hpow x hx).2
  have hOb : D.Pf l (Ob l) := ⟨(base l).natCast_l, (base l).perf.1⟩
  have hA : D.Pf l A.A := ⟨A.natCast_l, A.perf.1⟩
  obtain ⟨hts, htk⟩ := RL.tens A n
  have hbs := ((RL.base_acr (base l) isBase_base).2 n).1
  refine ⟨fun g hg => ?_, fun f f' h1 h2 h3 => ?_⟩
  · obtain ⟨⟨f₀, hf₀⟩, -⟩ := GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp g
    have hc : f₀.comp A.sW = h.comp ((base l).toAcr n) :=
      (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l (A := Ob l) _ n hOb hlB hlJ hJp (g.comp A.s)).2 _ _ fun a => by
        rw [RingHom.comp_apply, RingHom.comp_apply, sW, WittVector.map_teichmuller, hf₀]
        exact hg a
    have huv : ∀ r : Ainf l, (h.comp ((base l).cris n)) (algebraMap (Ainf l) (Acris l) r) =
        f₀ (algebraMap (Ainf l) A.W r) := fun r => by
      rw [RingHom.comp_apply, cris_algebraMap]
      have e : (base l).sW r = r := wmap_id r
      rw [e]
      exact (RingHom.congr_fun hc r).symm
    obtain ⟨f, hf1, hf2⟩ := tens_desc l n hts htk (h.comp ((base l).cris n)) f₀ huv hlB
    refine ⟨f, RingHom.ext fun y => ?_, fun a => ?_⟩
    · obtain ⟨a, rfl⟩ := hbs y
      rw [RingHom.comp_apply, mapAcr_cris]
      exact hf1 a
    · have e : f (A.toAcr n (WittVector.teichmuller l a)) = f₀ (WittVector.teichmuller l a) :=
        hf2 (WittVector.teichmuller l a)
      rw [e, hf₀]
  · have hfJ : A.PFil n ≤ (((base l).PFil n).map h).comap f := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact hlJ
      · rw [hFil 1, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply, h1]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hx)
    have hw := (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp
      ((Ideal.quotientMap _ f hfJ).comp π)).2 (f.comp (A.toAcr n)) (f'.comp (A.toAcr n))
      fun a => Ideal.Quotient.eq.2 (h3 a)
    refine tens_ext hts f f' (fun a => ?_) fun t => RingHom.congr_fun hw t
    have e : algebraMap (Acris l) (A.Acr n) a = mapAcr A.fromBase n ((base l).cris n a) :=
      (mapAcr_cris A.fromBase n a).symm
    rw [e]
    exact RingHom.congr_fun (h1.trans h2.symm) _

end GlobalTheory.CompanionTheory.AcrUniv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalPropertyStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.period_ring_universal_property : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.AcrUniv.maps_out | exact GlobalTheory.CompanionTheory.AcrUniv.maps_out | (intros; apply GlobalTheory.CompanionTheory.AcrUniv.maps_out <;> assumption)
end
end
