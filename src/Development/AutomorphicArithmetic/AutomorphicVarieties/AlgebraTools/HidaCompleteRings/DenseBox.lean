module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExistsPt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Order
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MuDvd

section

@[expose] public section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.mu_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧,
      (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
        (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
        ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  intro O _ _ _ ϖ hϖ f
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := by
    intro m
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := by
    intro m
    constructor
    · rintro ⟨g, rfl⟩ n
      rw [← map_pow, PowerSeries.coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      choose g hg using h
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := by
    intro m
    rw [hdvd, mu, le_iInf_iff]
    refine forall_congr' fun n => ?_
    rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := by
    intro h hzero
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    apply hc
    rw [← PowerSeries.coeff_map, hzero, map_zero]
  refine ⟨h1, ⟨hmu0, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
      ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    have hle := mu_le f n
    rw [hn] at hle
    exact le_antisymm hle bot_le
  · intro h
    have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      constructor
      · rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
          ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h]
      · intro i hi
        rw [PowerSeries.coeff_map]
        by_contra hne
        have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
        rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
        have hli : lam f ≤ i := Nat.sInf_le (by
          show addVal O (coeff i f) = mu f
          rw [hu, h])
        omega
    rw [hord, ENat.toNat_coe]
  · intro m
    have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := by
      intro n
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by
      rw [mu, mu, ENat.add_iInf]
      exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.coe_ne_top m) h, fun h => by rw [h]⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Weier

section

@[expose] public section

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.weier :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧, f ≠ 0 →
      ∃ (m : ℕ) (P : Polynomial O) (U : O⟦X⟧), mu f = m ∧ P.IsDistinguishedAt (maximalIdeal O) ∧ P.natDegree = lam f ∧
        IsUnit U ∧ f = C ϖ ^ m * (P : O⟦X⟧) * U := by
  intro O _ _ _ _ ϖ hϖ f hf
  have htop : mu f ≠ ⊤ := fun h => hf (mu_eq_top_iff.mp h)
  have hM := mu_dvd O ϖ hϖ
  obtain ⟨m, hmf⟩ : ∃ m : ℕ, (m : ℕ∞) = mu f := ⟨(mu f).toNat, ENat.coe_toNat htop⟩
  obtain ⟨g, hgf⟩ := ((hM f).1 m).mp hmf.le
  subst hgf
  obtain ⟨-, hzero, hlam, hshift⟩ := hM g
  obtain ⟨hmu, hl⟩ := hshift m
  have hg0 : mu g = 0 := by
    have h1 : (m : ℕ∞) + mu g = (m : ℕ∞) + 0 := by rw [add_zero, ← hmu, hmf]
    exact (WithTop.add_left_cancel (ENat.coe_ne_top m) h1)
  have hmap : (map (residue O)) g ≠ 0 := hzero.mp hg0
  obtain ⟨P, U, H⟩ := exists_isWeierstrassFactorization hmap
  refine ⟨m, P, U, hmf.symm, H.isDistinguishedAt, ?_, H.isUnit, ?_⟩
  · rw [hl, hlam hg0, H.natDegree_eq_toNat_order_map]
  · rw [mul_assoc, ← H.eq_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.DenseBox

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

private theorem algHom_mvPowerSeries_C_eq_algebraMap {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {σ : Type}
    (y : MvPowerSeries σ A →ₐ[A] K) (a : A) : y (MvPowerSeries.C a) = algebraMap A K a := by
  have h := y.commutes a
  simpa [MvPowerSeries.algebraMap_apply] using h

private theorem exists_injective_mvPowerSeries_last_to_powerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : ℕ) :
    ∃ S : MvPowerSeries (Fin (D + 1)) R →+* PowerSeries (MvPowerSeries (Fin D) R),
      Function.Injective S ∧
      (∀ a : R, S (MvPowerSeries.C a) = PowerSeries.C (MvPowerSeries.C a)) ∧
      S (MvPowerSeries.X (Fin.last D)) = PowerSeries.X ∧
      ∀ i : Fin D, S (MvPowerSeries.X i.castSucc) = PowerSeries.C (MvPowerSeries.X i) := by
  haveI hA : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin D) R) := UpperTheory.V.Alg.co_mvps R R (Fin D)
  haveI hB : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin (D + 1)) R) :=
    UpperTheory.V.Alg.co_mvps R R (Fin (D + 1))
  haveI hP : UpperTheory.V.Alg.IsCO R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) :=
    UpperTheory.V.Alg.co_mvps R (MvPowerSeries (Fin D) R) Unit
  have nX : ∀ (τ : Type) (s : τ), MvPowerSeries.X s ∈
      IsLocalRing.maximalIdeal (MvPowerSeries τ R) := by
    intro τ s
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have nX' : (MvPowerSeries.X () : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have hmem : ∀ s : Fin (D + 1), (Fin.lastCases (MvPowerSeries.X ())
      (fun i => MvPowerSeries.C (MvPowerSeries.X i)) s :
        MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _ := by
    intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [Fin.lastCases_last]
      exact nX'
    · rw [Fin.lastCases_castSucc, IsLocalRing.mem_maximalIdeal]
      intro h
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h
      exact (IsLocalRing.mem_maximalIdeal _).1 (nX (Fin D) i) h
  obtain ⟨S, ⟨hSC, hSX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries Unit (MvPowerSeries (Fin D) R))
    (Fin (D + 1)) (Algebra.ofId R _) _ hmem
  obtain ⟨ι, ⟨hιC, hιX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin D)
    (Algebra.ofId R _) (fun i => MvPowerSeries.X i.castSucc) (fun i => nX _ _)
  obtain ⟨T, ⟨hTC, hTX⟩, -⟩ := UpperTheory.V.Alg.co_ev R (MvPowerSeries (Fin D) R)
    (MvPowerSeries (Fin (D + 1)) R) Unit ι (fun _ => MvPowerSeries.X (Fin.last D)) (fun _ => nX _ _)
  obtain ⟨F, -, hF⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin (D + 1))
    (Algebra.ofId R _) MvPowerSeries.X (fun s => nX _ s)
  have hTS : T.comp S = AlgHom.id R _ := by
    have e1 := hF (T.comp S) ⟨fun x => ?_, fun s => ?_⟩
    · have e2 := hF (AlgHom.id R _) ⟨fun x => ?_, fun s => rfl⟩
      · rw [e1, e2]
      · simp [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply]
    · rw [AlgHom.comp_apply, hSC, Algebra.ofId_apply, AlgHom.commutes, Algebra.ofId_apply]
    · refine Fin.lastCases ?_ (fun i => ?_) s
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_last, hTX]
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_castSucc, hTC, hιX]
  refine ⟨S.toRingHom, fun x y h => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have h' : T (S x) = T (S y) := congrArg T h
    simpa [← AlgHom.comp_apply, hTS] using h'
  · have := hSC a
    simp only [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    exact this
  · exact (hSX (Fin.last D)).trans (by rw [Fin.lastCases_last]; rfl)
  · exact (hSX i.castSucc).trans (by rw [Fin.lastCases_castSucc]; rfl)

private theorem eq_zero_of_eval_eq_zero_on_infinite_unit_ball (l : ℕ) [Fact l.Prime] : ∀ (D : ℕ) (c : Coef l)
    (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) →
    ∀ f : MvPowerSeries (Fin D) c.O,
      (∀ (c' : Coef l) (y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l),
        (∀ g, y g ∈ c'.O) → (∀ i, y (MvPowerSeries.X i) ∈ Z i) → y f = 0) → f = 0 := by
  intro D
  induction D with
  | zero =>
    intro c Z hZ hn f hf
    obtain ⟨c', y, -, hy, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c (Fin 0) (fun i => i.elim0)
      (fun i => i.elim0)
    have h1 : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      ext n
      have hn0 : n = 0 := Subsingleton.elim _ _
      subst hn0
      simp
    have h2 := hf c' y hy (fun i => i.elim0)
    rw [h1, algHom_mvPowerSeries_C_eq_algebraMap] at h2
    have h3 : MvPowerSeries.constantCoeff f = 0 := Subtype.ext h2
    rw [h1, h3, map_zero]
  | succ D ih =>
    intro c Z hZ hn f hf
    haveI := c.dvr
    haveI := c.fin
    obtain ⟨hcpl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    obtain ⟨S, hSi, hSC, hSl, hSc⟩ := exists_injective_mvPowerSeries_last_to_powerSeries c.O D
    apply hSi
    rw [map_zero]
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    apply ih c (fun i => Z i.castSucc) (fun i => hZ _) (fun i => hn _)
    intro c'' y'' hint hX
    haveI := c''.dvr
    haveI := c''.fin
    obtain ⟨hcpl'', -⟩ := UpperTheory.V.abelian₂.dvr_finite l c''.O
    let ycr : MvPowerSeries (Fin D) c.O →+* c''.O := y''.toRingHom.codRestrict c''.O hint
    have hycr : ∀ x, ((ycr x : c''.O) : PadicAlgCl l) = y'' x := fun x => rfl
    have hg : PowerSeries.map ycr (S f) = 0 := by
      refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar c''.O (PadicAlgCl l) c''.O.val.toRingHom
        Subtype.val_injective _ (Z (Fin.last D)) (hZ _) ?_
      intro z hz
      obtain ⟨c3, ev, -, hev, hevX⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c'' Unit (fun _ => z)
        (fun _ => hn _ z hz)
      have hevC : ∀ b : c''.O, ev (PowerSeries.C b) = b := fun b => algHom_mvPowerSeries_C_eq_algebraMap ev b
      let G : MvPowerSeries (Fin (D + 1)) c.O →ₐ[c.O] PadicAlgCl l :=
        { toRingHom := ev.toRingHom.comp ((PowerSeries.map ycr).comp S)
          commutes' := by
            intro a
            show ev (PowerSeries.map ycr (S (algebraMap c.O _ a))) = _
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hSC,
              PowerSeries.map_C, hevC, hycr, algHom_mvPowerSeries_C_eq_algebraMap] }
      have hG : G f = 0 := by
        refine hf c3 G (fun g => hev _) (fun i => ?_)
        refine Fin.lastCases ?_ (fun j => ?_) i
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X (Fin.last D)))) ∈ _
          rw [hSl, PowerSeries.map_X]
          exact (hevX ()).symm ▸ hz
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X j.castSucc))) ∈ _
          rw [hSc, PowerSeries.map_C, hevC, hycr]
          exact hX j
      exact ⟨ev.toRingHom, fun a => hevC a, hevX (), hG⟩
    have h4 := congrArg (PowerSeries.coeff n) hg
    rw [PowerSeries.coeff_map, map_zero] at h4
    have h5 := congrArg Subtype.val h4
    rw [hycr] at h5
    exact h5

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.denseBox :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (D : ℕ) (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) → Sep {y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l | ∀ i, y (MvPowerSeries.X i) ∈ Z i} := by
  intro l _ c D Z hZ hn f hf
  exact eq_zero_of_eval_eq_zero_on_infinite_unit_ball l D c Z hZ hn f (fun c' y _ hX => hf y hX)
end
end
