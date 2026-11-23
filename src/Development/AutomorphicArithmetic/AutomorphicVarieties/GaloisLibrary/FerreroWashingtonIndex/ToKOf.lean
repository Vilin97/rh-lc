module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PhiDvd
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DescZRetr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nonvan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Struct
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FrobEig

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.frobEig :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) (k G A : Type) [Field k] [CharP k l] [CommGroup G] [CommRing A] [Algebra k A] (r : MonoidAlgebra k G →ₐ[k] A) (p : G →* G) (χ : G →* kˣ) (e : A) (θ : MonoidAlgebra k G), (∀ g, r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ l ^ a)) * e = ((χ g : k) ^ l ^ a) • e) → r θ ^ l ^ a * e = r (tw χ p θ) ^ l ^ a * e := by
  intro l _ a k G A _ _ _ _ _ r p χ e θ h
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  haveI : CharP A l := charP_of_injective_algebraMap (algebraMap k A).injective l
  set q := l ^ a with hq
  have frob_add : ∀ x y : A, (x + y) ^ q = x ^ q + y ^ q := fun x y => by
    rw [hq]
    exact add_pow_char_pow x y l a
  have hs : ∀ (x : G) (b : k), r (MonoidAlgebra.single x b) ^ q = b ^ q • r (MonoidAlgebra.of k G (x ^ q)) := by
    intro x b
    have e1 : MonoidAlgebra.single x b = b • MonoidAlgebra.of k G x := by
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
    rw [e1, map_smul, smul_pow, map_pow (MonoidAlgebra.of k G), map_pow r]
  induction θ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), frob_add, add_mul, hf, hg]
  | single g c =>
    rw [tw_single, hs, hs]
    have hg : g ^ q = (g * (p g)⁻¹) ^ q * (p g) ^ q := by
      rw [mul_pow, inv_pow, inv_mul_cancel_right]
    rw [hg, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc,
      mul_comm (r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ q))), mul_assoc, h g, mul_smul_comm,
      smul_smul, mul_pow]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepChar

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sepChar :
    ∀ (k D A : Type) [Field k] [IsAlgClosed k] [CommGroup D] [Finite D] [CommRing A] [Algebra k A] (ρ : D →* A) (x : A), (Nat.card D : k) ≠ 0 → (∀ (ψ : D →* kˣ) (e : A), (∀ d, ρ d * e = (ψ d : k) • e) → x * e = 0) → x = 0 := by
  intro k D A _ _ _ _ _ _ ρ x hD h
  classical
  letI := Fintype.ofFinite D
  have hexp : ((Monoid.exponent D : ℕ) : k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := Group.exponent_dvd_nat_card (G := D)
    apply hD
    rw [hc]; push_cast; rw [h0, zero_mul]
  haveI : NeZero ((Monoid.exponent D : ℕ) : k) := ⟨hexp⟩
  haveI : NeZero (Monoid.exponent D) := ⟨fun h0 => hexp (by rw [h0]; simp)⟩
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent D) := inferInstance
  have hcard : Nat.card (D →* kˣ) = Nat.card D :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity D k
  haveI : Finite (D →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  letI := Fintype.ofFinite (D →* kˣ)
  have h1 : ∀ ψ : D →* kˣ, x * (∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d) = 0 := by
    intro ψ
    apply h ψ
    intro g
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro d
    simp only [Equiv.coe_mulLeft, mul_smul_comm, smul_smul, ← map_mul, ← Units.val_mul]
    congr 3
    rw [mul_inv, mul_inv_cancel_left]
  have h2 : ∀ d : D, d ≠ 1 → ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
    intro d hd
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity D k (a := d⁻¹) (inv_ne_one.mpr hd)
    have e : ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = (φ d⁻¹ : k) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) := by
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft φ) _ _ ?_).symm
      intro ψ
      simp only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]
    have hne : ((φ d⁻¹ : kˣ) : k) ≠ 1 := fun h' => hφ (Units.val_eq_one.mp h')
    have : (1 - ((φ d⁻¹ : kˣ) : k)) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
      rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)
  have h3 : ∑ ψ : D →* kˣ, ∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d = (Nat.card D : k) • (1 : A) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (1 : D)]
    · rw [← hcard, Nat.card_eq_fintype_card]
      simp
    · intro d _ hd
      rw [h2 d hd, zero_smul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have h4 : x * ((Nat.card D : k) • (1 : A)) = 0 := by
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_eq_zero fun ψ _ => h1 ψ
  rw [mul_smul_comm, mul_one] at h4
  exact (smul_eq_zero.mp h4).resolve_left hD
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AlgK

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.algK :
    ∀ (l : ℕ) [Fact l.Prime] (a m b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [IsAlgClosed k] [CommGroup G] [Finite G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ J : G) (θ : MonoidAlgebra k G), m.Coprime l → γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, (g * (p g)⁻¹) ^ (l ^ a * m) = 1) → p J = 1 → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → (∀ χ : G →* kˣ, χ J = -1 → tw χ π θ ≠ 0) → (MonoidAlgebra.of k G γ - 1) ^ (l ^ K * l ^ a) ∈ Ideal.span {θ, 1 + MonoidAlgebra.of k G J} := by
  intro l _ a m b K k G Q _ _ _ _ _ _ p π γ J θ hml hγ hp hord hpJ hπ hπγ htw
  have hl : l.Prime := Fact.out
  let I : Ideal (MonoidAlgebra k G) := Ideal.span {θ, 1 + MonoidAlgebra.of k G J}
  let r : MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⧸ I) := Ideal.Quotient.mkₐ k I
  have hr : ∀ x, r x = 0 ↔ x ∈ I := fun x => by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem
  let qh : G →* G :=
    { toFun := fun g => (g * (p g)⁻¹) ^ (l ^ a)
      map_one' := by simp
      map_mul' := by
        intro x y
        rw [map_mul, mul_inv, mul_mul_mul_comm, mul_pow] }
  let D : Subgroup G := qh.range
  let qD : G →* D := qh.rangeRestrict
  have hcard : (Nat.card D : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k l] at h
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' l h
    obtain ⟨g, hg⟩ := d.2
    have h1 : (d : G) ^ m = 1 := by
      rw [← hg]
      show ((g * (p g)⁻¹) ^ (l ^ a)) ^ m = 1
      rw [← pow_mul]
      exact hord g
    have h2 : orderOf d ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using h1)
    rw [hd] at h2
    have h3 : l ∣ Nat.gcd m l := Nat.dvd_gcd h2 dvd_rfl
    rw [hml] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  let ρ : D →* (MonoidAlgebra k G ⧸ I) :=
    ((r : MonoidAlgebra k G →+* (MonoidAlgebra k G ⧸ I)) : MonoidAlgebra k G →* (MonoidAlgebra k G ⧸ I)).comp
      ((MonoidAlgebra.of k G).comp D.subtype)
  have hρ : ∀ g, ρ (qD g) = r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ (l ^ a))) := fun g => rfl
  have hθ : r θ = 0 := (hr θ).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hJ : r (MonoidAlgebra.of k G J) = -1 := by
    have h0 : r (1 + MonoidAlgebra.of k G J) = 0 :=
      (hr _).mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [map_add (f := _), map_one] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have hla : l ^ a ≠ 0 := pow_ne_zero _ hl.ne_zero
  rw [← hr]
  apply sepChar k D _ ρ _ hcard
  intro ψ e he
  by_cases he0 : e = 0
  · rw [he0, mul_zero]
  let F : k ≃+* k := (iterateFrobeniusEquiv k l a).symm
  let χ : G →* kˣ := (Units.map (F : k →* k)).comp (ψ.comp qD)
  have hχ : ∀ g, (χ g : k) ^ (l ^ a) = ψ (qD g) := by
    intro g
    show (F (ψ (qD g) : k)) ^ (l ^ a) = _
    rw [← iterateFrobeniusEquiv_def]
    exact RingEquiv.apply_symm_apply _ _
  have hT : r (tw χ p θ) ^ (l ^ a) * e = 0 := by
    have := frobEig l a k G _ r p χ e θ (by
      intro g
      rw [hχ g, ← hρ g]
      exact he (qD g))
    rw [← this, hθ, zero_pow hla, zero_mul]
  have hχJ : χ J = -1 := by
    have h1 := he (qD J)
    rw [hρ J, hpJ, inv_one, mul_one, map_pow, map_pow, hJ] at h1
    have h2 : ((-1 : k) ^ (l ^ a)) • e = (ψ (qD J) : k) • e := by
      rw [← h1, Algebra.smul_def, map_pow, map_neg, map_one]
    have h3 := smul_left_injective k he0 h2
    rw [← hχ J] at h3
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    apply (iterateFrobeniusEquiv k l a).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def]
    exact h3.symm
  obtain ⟨c, hc⟩ := phiDvd l b K k G Q p π γ χ θ hγ hp hπ hπγ (htw χ hχJ)
  rw [pow_mul, hc, mul_pow, map_mul, map_pow, map_pow, mul_right_comm, hT, zero_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToKOf

section

@[expose] public section

open UpperTheory.V.FW

private theorem toK_of (k G : Type) [CommRing k] [Monoid G] (g : G) :
    toK k G (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of k G g := by
  simp [toK]

theorem UpperTheory.V.FW.memZ :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ N n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)], n₀ ≤ n → ∃ γ : (ZMod (f * l ^ n))ˣ, (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * l ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * l ^ n))ˣ), (l : MonoidAlgebra ℤ (ZMod (f * l ^ n))ˣ)} := by
  intro l hl f c hf hc hc1 hcf
  have hp : l.Prime := hl.out
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hp.one_lt.ne' hf
  have ht : Nat.totient (f * l ^ ee l) ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hp.ne_zero)))).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht l hp.one_lt.ne'
  have hml : m.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  obtain ⟨n₀, h2, hnv⟩ := nonvan l f c hf hc hc1 hcf
  refine ⟨l ^ n₀ * l ^ a, n₀, h2, ?_⟩
  intro n _ hn
  have h : l ^ n₀ ∣ f * l ^ n := Dvd.dvd.mul_left (pow_dvd_pow l hn) f
  obtain ⟨γ, p, hγ, hγ1, hidx, hpz, hpow, hpJ, hπ⟩ := struct l f n hf (h2.trans hn)
  obtain ⟨hπ1, hπ2⟩ := hπ n₀ h hn
  refine ⟨γ, hγ, hidx, ?_⟩
  refine descZ l (AlgebraicClosure (ZMod l)) _ _ _ _ ?_
  have key := algK l a m n n₀ (AlgebraicClosure (ZMod l)) _ _ p (piQ l n₀ h) γ (-1)
    (toK (AlgebraicClosure (ZMod l)) _ (thetaH (f * l ^ n) c)) hml hγ1 hpz
    (fun g => by rw [← ham]; exact hpow g) hpJ hπ1 hπ2
    (fun χ hχ => hnv n h hn _ χ hχ)
  simpa only [map_pow, map_sub, map_add (f := _), map_one, toK_of] using key
end
end
