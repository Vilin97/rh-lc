module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.OneDim
import GroundTheory.AutomorphicForms.WhittakerDistribution
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourP
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.ContinuousLin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.PiZLin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.OrbP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.MemBzOfAdjoin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.DescFinal

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.AdjointSemisimple.AdjunctionCharZero

section

section

namespace PositivityTheory.RgUd.T.AdjPf

open Module PositivityTheory.RgUd.T

theorem dc {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hr : IsReduced Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), x * y = y * x) : x ∈ Z := by
  classical
  haveI : IsReduced Z := hr
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  haveI : IsSemisimpleModule Z (Fin n → k) := inferInstance
  have key : ∀ g : Module.End Z (Fin n → k), ∀ v : Fin n → k,
      Matrix.mulVec x (g v) = g (Matrix.mulVec x v) := by
    intro g v
    set y := LinearMap.toMatrix' (g.restrictScalars k) with hydef
    have hyv : ∀ w, Matrix.mulVec y w = g w := fun w => by
      rw [← Matrix.toLin'_apply, hydef, Matrix.toLin'_toMatrix']
      rfl
    have hy : y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro a ha
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hyv, hyv]
      exact (g.map_smul ⟨a, ha⟩ w).symm
    rw [← hyv, ← hyv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx y hy]
  let f : Module.End (Module.End Z (Fin n → k)) (Fin n → k) :=
    { toFun := fun v => Matrix.mulVec x v
      map_add' := Matrix.mulVec_add x
      map_smul' := fun g v => key g v }
  obtain ⟨r, hr'⟩ := jacobson_density (R := Z) f
    (Finset.univ.image (fun i : Fin n => (Pi.single i (1 : k) : Fin n → k)))
  have hxr : x = (r : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply]
    exact hr' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hxr]
  exact r.2

theorem isSemisimple_of_mem {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hr : IsReduced Z) (z : Matrix (Fin n) (Fin n) k) (hz : z ∈ Z) :
    Module.End.IsSemisimple (Matrix.toLin' z) := by
  set w : Z := ⟨z, hz⟩ with hw
  have hint : IsIntegral k w := IsIntegral.of_finite k w
  have hm0 : minpoly k w ≠ 0 := minpoly.ne_zero hint
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := minpoly k w) ?_ ?_
  · intro x hx
    obtain ⟨r, hr⟩ := hx
    have h1 : Polynomial.aeval w (x * r) = 0 := by
      apply IsReduced.eq_zero
      refine ⟨2, ?_⟩
      rw [pow_two, ← map_mul]
      have hsq : x * r * (x * r) = minpoly k w * r := by rw [hr]; ring
      rw [hsq, map_mul, minpoly.aeval, zero_mul]
    have h2 : minpoly k w ∣ x * r := minpoly.dvd k w h1
    have hxr : x * r ≠ 0 := by
      intro h
      apply hm0
      rw [hr, mul_assoc, h, mul_zero]
    rw [hr, mul_assoc] at h2
    have h3 : x * (x * r) ∣ 1 * (x * r) := by rwa [one_mul]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxr).mp h3)
  · have h0 : Polynomial.aeval z (minpoly k w) = 0 := by
      have h := congrArg Z.val (minpoly.aeval k w)
      rwa [map_zero, ← Polynomial.aeval_algHom_apply] at h
    have h4 := Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom z (minpoly k w)
    rw [h0, map_zero] at h4
    exact h4

end PositivityTheory.RgUd.T.AdjPf

namespace PositivityTheory.RgUd.T

open Module

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjunction_char_zero [CharZero k] : Adj (k := k) := by
  intro n Z hZ s hs hsZ hss
  obtain ⟨hc, hr⟩ := hZ
  set S : Set (Matrix (Fin n) (Fin n) k) := insert s (Z : Set (Matrix (Fin n) (Fin n) k)) with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (rfl | ha) b (rfl | hb)
    · rfl
    · exact (hs b hb).symm
    · exact hs a ha
    · exact hc a ha b hb
  have hSc : S ⊆ Subalgebra.centralizer k S := fun a ha =>
    (Subalgebra.mem_centralizer_iff k).mpr fun g hg => hS g hg a ha
  have hcomm : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ Subalgebra.centralizer k S := Algebra.adjoin_le hSc ha
    have hb' : b ∈ Subalgebra.centralizer k (Subalgebra.centralizer k S : Set (Matrix (Fin n) (Fin n) k)) :=
      Algebra.adjoin_le_centralizer_centralizer k S hb
    exact (Subalgebra.mem_centralizer_iff k).mp hb' a ha'
  have hsemi : ∀ x ∈ adj Z s, Module.End.IsSemisimple (Matrix.toLin' x) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hss
      · exact AdjPf.isSemisimple_of_mem Z hr x hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]
      exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
    | add x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [map_add (f := _)]
      exact Module.End.IsSemisimple.add_of_commute hcm ihx ihy
    | mul x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [Matrix.toLin'_mul, ← Module.End.mul_eq_comp]
      exact Module.End.IsSemisimple.mul_of_commute hcm ihx ihy
  refine ⟨⟨hcomm, ?_⟩, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    have hxs := hsemi x.1 x.2
    have hn : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k)) := by
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      have hm' : (x : Matrix (Fin n) (Fin n) k) ^ m = 0 := by
        rw [← Subalgebra.coe_pow, hm, Subalgebra.coe_zero]
      have h5 := congrArg (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) hm'
      rw [map_pow, map_zero] at h5
      exact h5
    have h6 := Module.End.eq_zero_of_isNilpotent_isSemisimple hn hxs
    exact Subtype.ext ((Matrix.toLin'.map_eq_zero_iff).mp h6)
  · have hsub : (Z : Set (Matrix (Fin n) (Fin n) k)) ⊆ (adj Z s : Set (Matrix (Fin n) (Fin n) k)) :=
      fun z hz => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
    have hle := Subalgebra.centralizer_le k _ _ hsub
    have hne : Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k)) ≠
        Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      intro h
      apply hsZ
      apply AdjPf.dc Z hc hr s
      intro y hy
      rw [← h] at hy
      exact (Subalgebra.mem_centralizer_iff k).mp hy s (Algebra.subset_adjoin (Set.mem_insert _ _))
    have hlt : Subalgebra.toSubmodule (Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k))) <
        Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
      lt_of_le_of_ne (Subalgebra.toSubmodule.monotone hle)
        (fun h => hne (Subalgebra.toSubmodule_injective h))
    exact Submodule.finrank_lt_finrank_of_lt hlt

end PositivityTheory.RgUd.T
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.BasePPf

section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.BasePf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem usage₁₀ [CharZero k] : BaseP (k := k) := by
  intro n Z hZ h0 ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

end PositivityTheory.RgUd.T.Nil
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.Assembly

section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem nilpB_of (fourP : FourP (k := k)) (orbP : OrbP (k := k)) (locQ : LocQ (k := k)) (baseP : BaseP (k := k)) :
    NilpB (k := k) := by
  unfold NilpB
  intro n Z hCR hH
  by_cases hd : dB0 Z = 0
  · exact baseP n Z hCR hd
  refine locQ n Z hCR fun y ξ hξ hinv => ?_
  have hmono : ∀ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp η (Fib Z y) → Supp η (Bz Z ×ˢ Set.univ) := by
    intro η hη f hf hvan
    refine hη f hf fun p hp => hvan p ?_
    have hp' : p ∈ (Bz Z ∩ qZ Z ⁻¹' {y}) ×ˢ (Set.univ : Set (Fin n → k)) := hp
    exact ⟨hp'.1.1, hp'.2⟩
  obtain ⟨t, ht0, ht1⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, hF4, hF5, hF6⟩ := fourP n Z hCR
  obtain ⟨a, ha, hP⟩ := orbP n Z hCR (Nat.pos_of_ne_zero hd) t ht1 y
  have hξB := hmono ξ hξ
  have hFξ := hP (𝓕 ξ) (hF2 ξ y hξ) (hF3 ξ hξB hinv) (hH (𝓕 ξ) (hF1 ξ hξB) (hF3 ξ hξB hinv))
  have hξK := hP ξ hξ hinv (hH ξ hξB hinv)
  have hc : 1 < (nabs k t)⁻¹ := one_lt_inv_iff₀.2 ⟨ht0, ht1⟩
  have key : ξ ∈ (supportedIn (UU : Set (Sp k n))).dualAnnihilator := by
    refine bez _ (pull Z t) (pull Z t⁻¹) (pull_inv Z hCR t).1 (pull_inv Z hCR t).2 ?_
      ((nabs k t)⁻¹) hc (dB0 Z) a ha ξ ?_ ?_
    · intro m hm
      rw [Submodule.mem_dualAnnihilator] at hm ⊢
      exact pull_kills Z hCR t m hm
    · rw [Submodule.mem_dualAnnihilator]
      exact hξK
    · rw [Submodule.mem_dualAnnihilator]
      refine (hF4 _ (prod_supp Z hCR t _ a ξ hξB)).2 ?_
      intro f hf
      have hfu : f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
        (show f ∈ supportedIn (Set.univ : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ Set.univ from Iff.rfl).2
          ⟨((show f ∈ supportedIn (UU : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ UU from Iff.rfl).1 hf).1,
            Set.subset_univ _⟩
      rw [four_prod Z hCR 𝓕 hF1 hF5 hF6 t a ξ hξB f hfu]
      exact hFξ f hf
  exact (Submodule.mem_dualAnnihilator ξ).1 key

end PositivityTheory.RgUd.T.Nil.Asm
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpB

section

section

namespace PositivityTheory.RgUd.T.Nil.Final

theorem nilpB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] :
    PositivityTheory.RgUd.T.NilpB (k := k) :=
  PositivityTheory.RgUd.T.Nil.Asm.nilpB_of k (PositivityTheory.RgUd.T.Nil.Four.Final.fourP k) (PositivityTheory.RgUd.T.Nil.Orb.Final.orbP k)
    (PositivityTheory.RgUd.T.Nil.Four.Final.locQ k) (PositivityTheory.RgUd.T.Nil.usage₁₀ k)

end PositivityTheory.RgUd.T.Nil.Final
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.LocStep

section

@[expose] public section

namespace PositivityTheory.RgUd.T.Final

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dich [CharZero k] : Dich (k := k) := PositivityTheory.RgUd.T.Alg.dich k
theorem adjP [CharZero k] : Adj (k := k) := adjunction_char_zero k
theorem locStep : LocStep (k := k) := LocStepPf.local_descent_holds
theorem descA [CharZero k] : DescA (k := k) := PositivityTheory.RgUd.T.Desc.Final.descA k
theorem nilpB [CharZero k] : NilpB (k := k) := PositivityTheory.RgUd.T.Nil.Final.nilpB k

theorem van_all [CharZero k] : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)),
    Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = m → CR Z → Van Z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    refine nilpB k n Z hZ fun ξ hs hi => locStep k n Z hZ ξ hs hi fun y => ?_
    rcases dich k n Z hZ y with h | ⟨s, hs, hsZ, hss, hy⟩
    · exact Or.inl h
    · obtain ⟨hC, hlt⟩ := adjP k n Z hZ s hs hsZ hss
      exact Or.inr fun ξ' h1 h2 => descA k n Z hZ s hs hsZ hss (ih _ (hm ▸ hlt) n _ rfl hC) y hy ξ' h1 h2

theorem thmT [CharZero k] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  exact van_all k _ n Z rfl ⟨hcomm, hred⟩ ξ (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩)
    (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.T.Final
end
end
