module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ComplOddPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatChi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.OBLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.FSurj
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrThick
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatSt

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.hat_st :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, H.r (H.T.st y) = (H.r y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hf H
  have key : ∀ g : G.G₀, (algebraMap B Bh) ↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) •
      ((mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)).map (algebraMap x.A (FractionRing x.A)) =
      (((mat x.ρ) (h.p₀ g)).map (algebraMap x.A (FractionRing x.A)))ᵀ := by
    intro g
    obtain ⟨he, hc⟩ := eps_eq P g
    have hunit : P.f (↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) : B) =
        ↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) := by
      have hu : Units.map (P.f : B →* x.A) ((G.frame.eps O B) g) =
          (G0.frame.eps ℤ_[l] x.A) (h.p₀ g) := by
        apply Units.ext
        rw [Units.coe_map]
        exact he
      rw [← hu, ← map_zpow (Units.map (P.f : B →* x.A)), Units.coe_map]
      rfl
    have hinvM : (mat x.ρ) (h.p₀ (G.frame.conj g)) * (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    have hA : ((mat x.ρ) (h.p₀ g))ᵀ =
        (↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) : x.A) •
          (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) := by
      have hform := x.form (h.p₀ g)
      rw [Units.val_one, Matrix.mul_one, ← hc] at hform
      calc ((mat x.ρ) (h.p₀ g))ᵀ = ((mat x.ρ) (h.p₀ g))ᵀ * ((mat x.ρ) (h.p₀ (G.frame.conj g)) *
            (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)) := by rw [hinvM, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hform, Matrix.smul_mul, Matrix.one_mul]
    rw [← Matrix.transpose_map, hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def, hf, hunit]
  intro y
  obtain ⟨z, rfl⟩ := H.surj y
  refine MonoidAlgebra.induction_on (motive := fun z => H.r (H.T.st (H.ι z)) = (H.r (H.ι z))ᵀ)
    z ?_ ?_ ?_
  · intro g
    rw [MonoidAlgebra.of_apply, H.st, map_smul, H.r_ι, H.r_ι]
    exact key g
  · intro a b ha hb
    simp only [map_add (f := _), ha, hb, Matrix.transpose_add]
  · intro c a ha
    simp only [map_smul, ha, Matrix.transpose_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RFSurj

section

@[expose] public section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem rF_surj : ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u)
    {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)],
    (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) →
    RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh →
    Function.Surjective (algebraMap Bh (FractionRing x.A)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hcomp hker z
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors x.A) z
  obtain ⟨a', rfl⟩ := (f_surj P).1 a
  obtain ⟨b', hb'⟩ := (f_surj P).1 (b : x.A)
  have hu : IsUnit (algebraMap B Bh b') := by
    by_contra hn
    have hm : algebraMap B Bh b' ∈ maximalIdeal Bh := (mem_maximalIdeal _).2 hn
    rw [← hker, RingHom.mem_ker, hcomp, hb'] at hm
    exact nonZeroDivisors.coe_ne_zero b
      ((IsFractionRing.injective x.A (FractionRing x.A)) (hm.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := hu
  refine ⟨algebraMap B Bh a' * ↑v⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hb', ← hcomp, ← hv, ← map_mul, mul_assoc,
    Units.inv_mul, mul_one, hcomp]

end UpperTheory.V.Pa
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepOf

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.urep_of :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → Nonempty (URep h x D I Bh (algebraMap Bh (FractionRing x.A)) e) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g hep hD
  letI : CommRing g.AA := g.ring
  letI : Algebra Bh g.AA := g.alg
  letI : Ring H.E := H.ring
  letI : Algebra Bh H.E := H.alg
  letI : Algebra B H.E := H.algB
  haveI : IsScalarTower B Bh H.E := H.tower
  letI algB : Algebra B g.AA := ((algebraMap Bh g.AA).comp (algebraMap B Bh)).toAlgebra
  haveI tower : IsScalarTower B Bh g.AA := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA :=
    ((g.φ.toRingHom.comp H.ι.toRingHom).toMonoidHom).comp (MonoidAlgebra.of Bh G.G₀)
  have hvr : ∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1)) := fun _ => rfl
  have key : ∀ w, GDet.repAlg vr g.AA (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA) w) =
      g.φ (H.ι (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh) w)) := by
    intro w
    have hext : ((GDet.repAlg vr g.AA).toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B g.AA))) =
        (g.φ.toRingHom.comp (H.ι.toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh)))) := by
      apply MonoidAlgebra.ringHom_ext
      · intro b
        have hs : MonoidAlgebra.single (1 : G.G₀) (algebraMap B Bh b) =
            (algebraMap B Bh b) • (1 : MonoidAlgebra Bh G.G₀) := by
          rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one, hs, map_smul]
        exact algebraMap_smul g.AA ((algebraMap B Bh) b) (1 : Matrix (Fin n) (Fin n) g.AA)
      · intro a
        simp only [RingHom.comp_apply, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, GDet.repAlg, MonoidAlgebra.lift_single, map_one]
        rw [one_smul]
        show (algebraMap g.AA g.AA).mapMatrix (vr a) = _
        rw [Algebra.algebraMap_self, RingHom.mapMatrix_id]
        rfl
    exact congrArg (fun f => f w) hext
  let f := g.φ.toLinearMap.restrictScalars B
  refine ⟨{
    AA := g.AA
    ring := g.ring
    alg := g.alg
    algB := algB
    tower := tower
    fin := g.fin
    inj := g.inj
    N := g.N
    compl := g.compl
    mul_mem := g.mul_mem
    typeI := g.typeI
    vr := vr
    span := ?_
    det := gr_det H g hep hD vr hvr
    form := ?_
    red := ?_
    kills := ?_
    thick := gr_thick H g
    P := Submodule.map f H.P
    ker_le_span_sub_sup_map := H.ker_le_span_sub_sup_map.map f
    vr_mem := fun γ => Submodule.mem_map_of_mem (H.mem γ)
    cont := ?_ }⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact (g.range _).mp ⟨_, rfl⟩
    · intro Y hY
      obtain ⟨y, rfl⟩ := (g.range Y).mpr hY
      obtain ⟨z, rfl⟩ := H.surj y
      clear hY
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]
        exact Submodule.add_mem _ ha hb
      | single γ c =>
        have hc : (MonoidAlgebra.single γ c : MonoidAlgebra Bh G.G₀) = c • MonoidAlgebra.single γ 1 := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hc, map_smul, map_smul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨γ, rfl⟩)
  · intro γ
    have h1 : (vr γ)ᵀ = (algebraMap B Bh ↑(e γ ^ (1 - (n : ℤ)))) • vr (G.frame.conj γ)⁻¹ := by
      rw [hvr, ← g.st, H.st, map_smul]
      rfl
    rw [h1, smul_mul_assoc, ← map_mul, inv_mul_cancel, map_one, ← algebraMap_smul g.AA]
    rfl
  · intro γ i j b hb
    have := g.red (H.ι (MonoidAlgebra.single γ 1)) i j b hb
    rw [H.r_ι, Matrix.map_apply] at this
    exact this
  · intro z hz
    rw [key, (H.ker _).mpr (TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩), map_zero]
  · intro j
    obtain ⟨V, hV⟩ := H.cont j
    refine ⟨V, fun γ v hv => ?_⟩
    rw [← Submodule.map_smul'']
    have hm := Submodule.mem_map_of_mem (f := f) (hV γ v hv)
    rw [map_sub] at hm
    exact hm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.S6

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem s6 : S6 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ rF hl hc hr hk
  letI : Algebra Bh (FractionRing x.A) := rF.toAlgebra
  have hk' : RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh := hk
  obtain ⟨H⟩ := hat_ex P (Bh := Bh) hr
  have hs := rF_surj P (Bh := Bh) hr hk'
  haveI := hc.noeth
  haveI := hc.complete
  haveI := H.fin
  have h2 : IsUnit (2 : Bh) := by
    by_contra hn
    have h3 : (2 : Bh) ∈ RingHom.ker (algebraMap Bh (FractionRing x.A)) := by rw [hk']; exact hn
    rw [RingHom.mem_ker, map_ofNat] at h3
    have h4 : (2 : x.K) = 0 := by
      have h5 : (algebraMap x.A (FractionRing x.A)).comp (PowerSeries.C (R := x.K)) 2 = 0 := by rw [map_ofNat]; exact h3
      exact (map_eq_zero _).1 h5
    have h6 : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hl ?_)
      have h7 : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
      rw [PadicInt.norm_int_lt_one_iff_dvd] at h7
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 (by exact_mod_cast h7)
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_ofNat, h4] at h8
    exact not_isUnit_zero h8
  have hst := hat_st P hr H
  have hrg := hat_range P hs H
  obtain ⟨U, hx, hrk⟩ := idem x.a H.DE H.T H.r x.a_pos x.a_le h2 H.ch H.tr hk' (hat_chi P hr H) hst
    fun Z hZ => (hrg Z).1 hZ
  have hg : Nonempty (GrAlg H.T n x.a H.r U.ep) := by
    rcases x.a_le.lt_or_eq with ha | ha
    · exact gr_E x.a H.T H.r U x.a_pos ha hk' hst hx fun y => (hrg _).2 ⟨y, rfl⟩
    · have hn : 1 ≤ n := ha ▸ x.a_pos
      revert U
      rw [ha]
      intro U hx _
      exact gr_I H.T H.r U hn hst hx
  obtain ⟨g⟩ := hg
  exact urep_of H g U.coi hrk

end UpperTheory.V.Pa
end
end
