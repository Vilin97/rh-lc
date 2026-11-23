module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.GroupTheory.PGroup
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Filtration
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
public import Mathlib.Data.Matrix.Mul
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.CharP.Algebra

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AdicCharUnipotentPgroupQuotient

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.adic_char_unipotent_pgroup_quotient :
    ∀ {l : ℕ} [Fact l.Prime] {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [CharP Q l] [Finite (ResidueField Q)] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* Q) (h : ℕ), h ≠ 0 → AdicCont (maximalIdeal Q) χ → (∀ g, χ g - 1 ∈ maximalIdeal Q) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : G →* A, IsOpen (ψ.ker : Set G) → (∀ g g', χ g = χ g' → ψ g = ψ g') → ∀ g, ψ g ^ h = 1) → ∀ g, χ g = 1 := by
  intro l hl Q _ _ _ _ _ hfin G _ _ χ h hh hc hm H g
  have hp : l.Prime := hl.out
  have krull : ∀ x : Q, (∀ N : ℕ, Ideal.Quotient.mk (maximalIdeal Q ^ N) x = 1) → x = 1 := by
    intro x hx
    have h0 : x - 1 ∈ (⨅ N : ℕ, maximalIdeal Q ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      rw [← Ideal.Quotient.eq, hx N, map_one]
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top, Ideal.mem_bot] at h0
    exact sub_eq_zero.mp h0
  have unip : ∀ (N : ℕ) (g : G), Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (maximalIdeal Q ^ N)), Ideal.Quotient.eq]
    have : χ g ^ l ^ N - 1 = (χ g - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
    rw [this]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hp.one_lt).le (Ideal.pow_mem_pow (hm g) _)
  have hpow : χ g ^ h = 1 := by
    apply krull
    intro N
    haveI : Finite (Q ⧸ maximalIdeal Q) := hfin
    haveI : Finite (Q ⧸ maximalIdeal Q ^ N) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let φ : G →* (Q ⧸ maximalIdeal Q ^ N)ˣ :=
      ((Ideal.Quotient.mk (maximalIdeal Q ^ N)).toMonoidHom.comp χ).toHomUnits
    have hφ : ∀ g, (φ g : Q ⧸ maximalIdeal Q ^ N) = Ideal.Quotient.mk _ (χ g) := fun g => rfl
    have hP : IsPGroup l φ.range := by
      rintro ⟨_, g, rfl⟩
      refine ⟨N, Subtype.ext (Units.ext ?_)⟩
      simpa [hφ] using unip N g
    have hO : IsOpen (φ.rangeRestrict.ker : Set G) := by
      have := (hc N).isOpen_fiber 1
      convert this using 1
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [← hφ, Units.val_eq_one, Subtype.ext_iff]
      rfl
    have := H φ.range hP φ.rangeRestrict hO
      (fun g g' e => Subtype.ext (Units.ext (by
        change (φ g : Q ⧸ maximalIdeal Q ^ N) = φ g'
        rw [hφ, hφ, e]))) g
    have h2 : φ g ^ h = 1 := congrArg Subtype.val this
    rw [map_pow, ← hφ, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨a, h', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hp.ne_one
  have h3 : χ g ^ h' = 1 := by
    have : (χ g ^ h' - 1) ^ l ^ a = 0 := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hpow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero) |>.mp this)
  apply krull
  intro N
  have h4 : Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ h' = 1 := by
    rw [← map_pow, h3, map_one]
  have hcop : Nat.Coprime (l ^ N) h' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have h5 : orderOf (Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g)) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (unip N g)) (orderOf_dvd_of_pow_eq_one h4)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTer

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk64.diag_mul :
    ∀ {n : ℕ} {Q : Type} [inst : CommRing Q]
    (a b : Matrix (Fin n) (Fin n) Q),
    (∀ (i j : Fin n), i < j → a i j = (0 : Q)) →
      (∀ (i j : Fin n), i < j → b i j = (0 : Q)) → ∀ (i : Fin n), (a * b) i i = a i i * b i i := by
  intro n Q _ a b ha hb i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hb j i h, mul_zero]
  · rw [ha i j h, zero_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TriangularRepresentationDiagonal

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem diag_mul {n : ℕ} {Q : Type} [CommRing Q] (a b : Matrix (Fin n) (Fin n) Q)
    (ha : ∀ i j, i < j → a i j = 0) (hb : ∀ i j, i < j → b i j = 0) (i : Fin n) :
    (a * b) i i = a i i * b i i :=
  _root_.UpperTheory.Reformulated.B.Qk64.diag_mul a b ha hb i

private theorem key {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q]
    [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q) (hc : ρ.Cont (maximalIdeal Q))
    (hb : (ρ.map (residue Q)).IsBar ((residue Q).comp f)) (ht : ρ.triM = ⊥) (h : ℕ) (h0 : h ≠ 0) (i : Fin n)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : F.G0 →* A, IsOpen (ψ.ker : Set F.G0) →
      (∀ g g', ρ.r g i i = ρ.r g' i i → F.Ψ g ^ w n i = F.Ψ g' ^ w n i → ψ g = ψ g') → ∀ g, ψ g ^ h = 1)
    (g : F.G0) : ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  haveI : CharP Q l := charP_of_injective_ringHom f.injective l
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  let χ : F.G0 →* Q :=
    { toFun := fun g => ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, diag_mul _ _ (hz a) (hz b), Subgroup.coe_mul, map_mul, mul_zpow, mul_inv, Units.val_mul,
          map_mul]
        ring }
  have hχ : ∀ g, χ g = ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) := fun _ => rfl
  have hinv : ∀ g : F.G0, f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g :=
    (lc_of_ker F.Ψ hF.Ψ_open).comp_continuous continuous_subtype_val
  have h1 : χ g = 1 := by
    refine adic_char_unipotent_pgroup_quotient (l := l) χ h h0 (fun N => ?_) (fun g => ?_) (fun A _ _ hA ψ hψ hh => H A hA ψ hψ ?_) g
    · have := (hc.1 i i N).mul (hΨ.comp fun u : kˣ =>
        Ideal.Quotient.mk (maximalIdeal Q ^ N) (f (((u ^ w n i)⁻¹ : kˣ) : k)))
      convert this using 1
      ext x
      simp [χ, map_mul]
    · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero, hχ, map_mul]
      have h2 : residue Q (ρ.r g i i) = residue Q (f ((F.Ψ g ^ w n i : kˣ) : k)) := hb.1 g i
      rw [h2, ← map_mul, mul_comm, hinv, map_one]
    · intro g g' e1 e2
      exact hh g g' (by rw [hχ, hχ, e1, e2])
  rw [hχ] at h1
  calc ρ.r g i i = ρ.r g i i * (f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k)) := by
        rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

theorem UpperTheory.V.Fr.triangular_representation_diagonal :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q), ρ.Cont (maximalIdeal Q) → (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → ∀ {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ), h ≠ 0 → (∀ a, F.Ψ (s a) = 1) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1)) → (∀ a (i : Fin n), (i : ℕ) = 0 → ρ.r (s a) i i = 1) → (∀ a (i : Fin n), w n i = 0 → ρ.r (s' a) i i = 1) → ∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  intro l _ k _ _ F C₀ n hF hn Q _ _ _ _ _ f ρ hc hb ht ι ι' s s' h h0 hs H h1 h2
  obtain ⟨-, -, sΨ, -, sr⟩ := UpperTheory.V.Fr.star hF
  have A0 : ∀ (i : Fin n), (i : ℕ) = 0 → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := fun i hi =>
    key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).1 fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h1 a i hi]; simp
      · rw [hs a]; simp
  have A1 : ∀ (i : Fin n), w n i = 0 → i.rev = i → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) :=
    fun i hi hr => key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).2
      (fun g => hh _ _ (by rw [sr, hr]) (by simp [hi])) fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h2 a i hi]; simp
      · simp [hi]
  have A2 : ∀ (i : Fin n), (i : ℕ) = 0 → w n i.rev = - w n i →
      ∀ g, ρ.r g i.rev i.rev = f ((F.Ψ g ^ w n i.rev : kˣ) : k) := fun i hi hw g => by
    rw [← sr, A0 i hi, sΨ, hw, _root_.zpow_neg, _root_.inv_zpow]
  intro g i
  rcases hn with rfl | rfl
  · fin_cases i
    · exact A0 0 rfl g
    · exact A2 0 rfl (by decide) g
  · fin_cases i
    · exact A0 0 rfl g
    · exact A1 1 (by decide) (by decide) g
    · exact A2 0 rfl (by decide) g
end
end
