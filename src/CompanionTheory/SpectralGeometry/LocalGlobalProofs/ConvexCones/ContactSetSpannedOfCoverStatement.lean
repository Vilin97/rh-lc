module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDefStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMemStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjection

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem eq_zero_of_zsmul_eq_zero_of_projective {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {n : ℤ} (hn : n ≠ 0) {z : P} (h : n • z = 0) : z = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O P)
  have hs' : ∀ x, Finsupp.linearCombination O (id : P → P) (s x) = x := fun x => LinearMap.congr_fun hs x
  have h0 : s z = 0 := by
    ext i
    have h1 : n • s z = 0 := by rw [← map_zsmul, h, map_zero]
    have h2 : (n : O) * s z i = 0 := by
      have := DFunLike.congr_fun h1 i
      simpa [zsmul_eq_mul] using this
    have h3 : (n : O) ≠ 0 := by exact_mod_cast hn
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  rw [← hs' z, h0, map_zero]

theorem IsPosDef.eq_zero_of_apply_self {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {B : P →ₗ[ℤ] P →ₗ[ℤ] ℝ} (h : IsPosDef B) {z : P}
    (hz : B z z = 0) : z = 0 := by
  by_contra hne
  have hli : LinearIndependent ℤ ![z] := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_contra hi
    exact hne (eq_zero_of_zsmul_eq_zero_of_projective (O := O) hi (by simpa using hg))
  have := h 1 _ hli ![1] (by simp)
  simp [hz] at this

theorem exists_psdCone_descend (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hr : Function.Surjective r) (hB : B ∈ psdCone (bar := bar) (X := X))
    (hk : ∀ y, r y = 0 → B y y = 0) : ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  obtain ⟨X', _, _, _, r', B', hr', h1, h2, h3⟩ := hB
  have hker : LinearMap.ker r ≤ LinearMap.ker r' := fun y hy =>
    IsPosDef.eq_zero_of_apply_self (O := O) h2 (by rw [← h3]; exact hk y hy)
  let s : X₁ →ₗ[O] X' := ((LinearMap.ker r).liftQ r' hker) ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
  have hs : ∀ x, s (r x) = r' x := fun x => by
    have : (r.quotKerEquivOfSurjective hr).symm (r x) = (LinearMap.ker r).mkQ x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun z => by
    obtain ⟨x, rfl⟩ := hr' z
    exact ⟨r x, hs x⟩
  refine ⟨pullR s B', ⟨X', _, _, inferInstance, s, B', hsurj, h1, h2, fun _ _ => rfl⟩, ?_⟩
  ext a b
  simp [h3, hs]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjectionStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_descends_along_surjection : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), Function.Surjective r → B ∈ psdCone (bar := bar) (X := X) → (∀ y, r y = 0 → B y y = 0) → ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupport

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_smul_mem_of_le_of_finrank_le {M : Type} [AddCommGroup M] [Module.Finite ℤ M] {P Q : Submodule ℤ M}
    (h : P ≤ Q) (hr : Module.finrank ℤ Q ≤ Module.finrank ℤ P) {y : M} (hy : y ∈ Q) :
    ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ P := by
  have e : (P.comap Q.subtype) ≃ₗ[ℤ] P := Submodule.comapSubtypeEquivOfLe h
  have h1 := Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)
  rw [e.finrank_eq] at h1
  have h2 : Module.finrank ℤ (Q ⧸ P.comap Q.subtype) = 0 := by omega
  obtain ⟨n, hn, hz⟩ := Module.finrank_eq_zero_iff.1 h2 (Submodule.Quotient.mk ⟨y, hy⟩)
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  simpa using hz

theorem diag_eq_zero_iff_of_isPosDef {X₁ : Type} [AddCommGroup X₁] {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B) (z : X₁) :
    B z z = 0 ↔ z ∈ Submodule.torsion ℤ X₁ := by
  constructor
  · intro h0
    by_contra hz
    have hy : LinearIndependent ℤ ![z] := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_contra hi
      have hg' : g 0 • z = 0 := by simpa using hg
      exact hz ((Submodule.mem_torsion_iff _).2 ⟨⟨g 0, mem_nonZeroDivisors_of_ne_zero hi⟩, hg'⟩)
    have := h 1 _ hy ![1] (by simp)
    simp [h0] at this
  · intro hz
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hz
    have ha' : (a : ℤ) • z = 0 := ha
    have h1 : ((a : ℤ) : ℝ) * B z z = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, ha', map_zero]
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast nonZeroDivisors.ne_zero a.2)

theorem exists_radical_of_mem_psdCone {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ N : Submodule ℤ X, ∀ y, y ∈ N ↔ B y y = 0 := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := hB
  refine ⟨(Submodule.torsion ℤ X₁).comap r.toAddMonoidHom.toIntLinearMap, fun y => ?_⟩
  rw [h2, diag_eq_zero_iff_of_isPosDef h1]
  rfl

theorem exists_least_radical : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)),
    K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) →
      ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  intro O _ _ _ _ bar X _ _ _ K hne hK hadd
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  choose! N hN using fun B (hB : B ∈ K) => exists_radical_of_mem_psdCone (hK hB)
  have hnn : ∀ B ∈ K, ∀ y, 0 ≤ B y y := fun B hB y => nonneg_of_mem_psdCone (hK hB) y
  obtain ⟨B₁, hB₁, hmin⟩ : ∃ B₁ ∈ K, ∀ B ∈ K, Module.finrank ℤ (N B₁) ≤ Module.finrank ℤ (N B) :=
    ⟨Function.argminOn (fun B => Module.finrank ℤ (N B)) K hne, Function.argminOn_mem _ _ hne,
      fun B hB => Function.argminOn_le (fun B => Module.finrank ℤ (N B)) K hB⟩
  refine ⟨B₁, hB₁, fun B hB y hy => ?_⟩
  have hsum := hadd B hB B₁ hB₁
  have hle : N (B + B₁) ≤ N B₁ := fun z hz => by
    have h0 : B z z + B₁ z z = 0 := by simpa using (hN _ hsum z).1 hz
    exact (hN _ hB₁ z).2 (by linarith [hnn B hB z, hnn B₁ hB₁ z])
  obtain ⟨n, hn, hny⟩ := exists_smul_mem_of_le_of_finrank_le hle (hmin _ hsum) ((hN _ hB₁ y).2 hy)
  have h0 : B (n • y) (n • y) + B₁ (n • y) (n • y) = 0 := by simpa using (hN _ hsum _).1 hny
  have h1 : B (n • y) (n • y) = 0 := by linarith [hnn B hB (n • y), hnn B₁ hB₁ (n • y)]
  have h2 : ((n : ℝ) * (n : ℝ)) * B y y = 0 := by
    rw [← h1]
    simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hn))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupportStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_exists_maximal_support : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)), K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) → ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCover

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

theorem isMin2_pullR_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (y : X) :
    IsMin2 (pullR r B) y ↔ IsMin2 B (r y) := by
  have e : ∀ x : X, r (y + (x + x)) = r y + (r x + r x) := fun x => by rw [map_add (f := _), map_add (f := _)]
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := hr x
    have := h x
    simp only [pullR_apply, e] at this
    exact this
  · intro h x
    simp only [pullR_apply, e]
    exact h (r x)

theorem pullR_mem_contact {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (h : B ∈ contact bar fun i => r (a i)) : pullR r B ∈ contact bar a :=
  ⟨pullR_mem_psdCone hr h.1, fun i => (isMin2_pullR_iff hr B (a i)).2 (h.2 i)⟩

theorem mem_contact_of_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (hB : B ∈ psdCone (bar := bar) (X := X₁)) (h : pullR r B ∈ contact bar a) : B ∈ contact bar fun i => r (a i) :=
  ⟨hB, fun i => (isMin2_pullR_iff hr B (a i)).1 (h.2 i)⟩

end Pull

theorem isSpanned_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
      Covers2 a → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar red X _ _ _ _ ι _ a ha
  have hadd : ∀ B ∈ contact bar a, ∀ B' ∈ contact bar a, B + B' ∈ contact bar a := fun B hB B' hB' =>
    ⟨GlobalTheory.T.psd_cone_add_mem O bar X B B' hB.1 hB'.1, fun i x => by
      have h1 := hB.2 i x
      have h2 := hB'.2 i x
      simp only [LinearMap.add_apply]
      exact add_le_add h1 h2⟩
  obtain ⟨B₁, hB₁, hrad⟩ := GlobalTheory.T.psd_cone_exists_maximal_support O bar X (contact bar a) ⟨0, zero_mem_contact bar a⟩ (fun B hB => hB.1) hadd
  obtain ⟨X₁, _, _, _, r, B₁', hr, hbal, hdef, hfac⟩ := id hB₁.1
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  have hfac' : B₁ = pullR r B₁' := LinearMap.ext₂ hfac
  have hB₁' : B₁' ∈ contact bar fun i => r (a i) :=
    mem_contact_of_pullR hr (hdef.mem_psdCone hbal) (hfac' ▸ hB₁)
  have hcov : Covers2 fun i => r (a i) := fun y => by
    obtain ⟨y, rfl⟩ := hr y
    obtain ⟨i, x, rfl⟩ := ha y
    exact ⟨i, r x, by rw [map_add (f := _), map_add (f := _)]⟩
  obtain ⟨m, γ, hγ, hnn, hK, hsub⟩ :=
    GlobalTheory.T.contact_set_spans_of_pos_def O bar X₁ ι (fun i => r (a i)) (red X₁) hcov ⟨B₁', hB₁', hdef⟩
  refine ⟨m, fun i => pull r (γ i), fun i => pull_mem r (hγ i), fun i y => hnn i (r y), fun i => ?_, fun B hB => ?_⟩
  · have e : toReal (pull r (γ i)) = pullR r (toReal (γ i)) := LinearMap.ext₂ fun _ _ => by simp
    rw [e]
    exact pullR_mem_contact hr (hK i)
  · have hker : ∀ y, r y = 0 → B y y = 0 := fun y hy => hrad B hB y (by rw [hfac, hy]; simp)
    obtain ⟨B', hB', rfl⟩ := GlobalTheory.T.psd_cone_descends_along_surjection O bar X X₁ r B hr hB.1 hker
    obtain ⟨t, ht, e⟩ := hsub (mem_contact_of_pullR hr hB' hB)
    refine ⟨t, ht, LinearMap.ext₂ fun y z => ?_⟩
    simp [e, LinearMap.sum_apply]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCoverStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.contact_set_spanned_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), Covers2 a → IsSpanned bar (contact bar a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact <;> assumption)
end
end
