module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantIdentities
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PpSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResLeMemDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResidueEqOneOfMap
import Mathlib.Tactic.Basify

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiDet

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [CommRing B] [CommRing A] [Group H] [Group G] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace G] (I : Ideal B) [IsHausdorff I B] (f : B →+* A), Function.Injective f → ∀ (π : H →* G), Function.Surjective π → Topology.IsQuotientMap π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → B[X]), (∀ g, (cp g).map f = (ρ g).charpoly) → (∀ j, AdicCont I fun g => (cp g).coeff j) → (∀ U : Subgroup H, IsClosed (U : Set H) → ρ.ker ≤ U → π.ker ≤ U) → ∃ D : W.GDet n B G, (D.comap π).map f = W.GDet.ofRep ρ ∧ (∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g) ∧ D.IsCont I :=
  _root_.UpperTheory.Reformulated.B.DeterminantIdentities.phiDet
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiFlag

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v : W.Vl l T.L, W.HasFlag ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) fun i => W.pushCh (algebraMap X.B X.A) (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v
  have hlow := X.pair.low (K.e v)
  have h1 : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := by
    have h0 := hlow.1
    simpa [UpperTheory.V.GradeZeroInterpolatingElement.IsGSp] using h0
  have h2 : X.P.n (K.e v) * adj (X.P.n (K.e v)) = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩, fun s => ?_⟩
  obtain ⟨s, hs⟩ := s
  have hs' : resLe T.F_le s ∈ (T.fr ∅).Gv (K.e v) := by
    show resLe T.F_le s ∈ Dec (F := T.F) (T.pl (K.e v))
    rw [← K.hA v]
    exact hs
  have hval : (((⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A) *
      ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) ⟨s, hs⟩ *
      (⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A)⁻¹ : GL (Fin 4) X.A) :
        Matrix (Fin 4) (Fin 4) X.A) =
      (algebraMap c'.O X.A (K.sc n s)) • (adj (X.P.n (K.e v)) * X.P.r (resLe T.F_le s) * X.P.n (K.e v)) := by
    simp [UpperTheory.V.Ws.Link.rho_apply, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, X.pair.flag (K.e v) _ hs' i j hij, smul_zero]
  · rw [hval, Matrix.smul_apply]
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i ⟨s, hs⟩, map_mul, ← IsScalarTower.algebraMap_apply, X.ψ_map _ _ _ hs', smul_eq_mul]
    rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiUnr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ K.V.S' → Ine (F := T.L) A ≤ (K.rho X n).ker := by
  intro Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg
  have hS : v ∉ K.s.S := by rw [← K.hV]; exact hv
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro hlt
    apply hS
    left
    apply (hA (l : 𝓞 (W.Lp T.L))).1
    simpa using hlt
  obtain ⟨hκ, hr⟩ := K.unr A v hA hS g hg
  have hβ : K.β g = 1 := K.β_t (K.t_unr A hl hg)
  have hmem : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' : p = l := by simpa using hp
      rw [hp']
      exact hl
    · exact hg
    · have he : resQ T.F (resLe T.F_le g) = resQ T.L g := by
        ext x
        rfl
      rw [he]
      exact hr
  rw [MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]
  have hsc : K.sc n g = 1 := by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]
  rw [hsc, map_one, one_smul]
  exact X.pair.kill _ hmem
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.SpacePsiMul

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiPsiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∃ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ := by
  intro Ω _ _ _ l _ c D T c' h K X n
  have hmem : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)),
      resLe (Tower.F_le T) (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    show _ ∈ Dec (T.pl (K.e v))
    have hg : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := K.hA v ▸ g.2
    exact hg
  have hup : ∀ (M N : GradeZeroInterpolatingElement.M4 X.A), IsUp M → IsUp N → ∀ i, (M * N) i i = M i i * N i i := by
    intro M N hM hN i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hM i k hlt, zero_mul]
      · rw [hN k i hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hleft : ∀ w, adj (X.P.n w) * X.P.n w = 1 := by
    intro w
    have h1 := (X.pair.low w).1
    simpa [IsGSp] using h1
  have hright : ∀ w, X.P.n w * adj (X.P.n w) = 1 := fun w => mul_eq_one_comm.mp (hleft w)
  have hPmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.P.ψ w i (s * t) = X.P.ψ w i s * X.P.ψ w i t := by
    intro w i s hs t ht
    have key : adj (X.P.n w) * X.P.r (s * t) * X.P.n w
        = (adj (X.P.n w) * X.P.r s * X.P.n w) * (adj (X.P.n w) * X.P.r t * X.P.n w) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.P.n w) (adj (X.P.n w)), hright w, Matrix.one_mul]
    unfold PD.ψ
    rw [key]
    exact hup _ _ (X.pair.flag w s hs) (X.pair.flag w t ht) i
  have hψmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.ψ w i (s * t) = X.ψ w i s * X.ψ w i t := by
    intro w i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map w i _ (mul_mem hs ht), X.ψ_map w i s hs, X.ψ_map w i t ht]
    exact hPmul w i s hs t ht
  have hψone : ∀ w i, X.ψ w i 1 = 1 := by
    intro w i
    apply X.inj
    rw [map_one, X.ψ_map w i 1 (one_mem _)]
    unfold PD.ψ
    rw [map_one, Matrix.mul_one, hleft w, Matrix.one_apply_eq]
  have hψunit : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, IsUnit (X.ψ w i s) := by
    intro w i s hs
    by_contra hne
    have h0 : IsLocalRing.residue X.B (X.ψ w i s) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hne)
    have hr := X.ψ_red w i s hs
    have hu := ((((T.fr ∅).χ i s).isUnit.map (inc h)).map (IsLocalRing.residue c'.O))
    rw [← hr] at hu
    simp only [res, h0] at hu
    simp at hu
    exact hne hu
  have hsc : ∀ g g' : G T.L Ω, K.sc n (g * g') = K.sc n g * K.sc n g' := by
    intro g g'
    unfold Link.sc
    simp only [map_mul, Units.val_mul, mul_pow]
    ring
  have hsc1 : K.sc n 1 = 1 := by
    unfold Link.sc
    simp
  have hscu : ∀ g : G T.L Ω, IsUnit (K.sc n g) := by
    intro g
    exact (K.κ g).isUnit.mul ((K.β g).isUnit.pow n)
  refine ⟨fun v i => IsUnit.liftRight
    { toFun := fun g => algebraMap c'.O X.B (K.sc n (g : G T.L Ω)) *
        X.ψ (K.e v) i (resLe (Tower.F_le T) (g : G T.L Ω))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one, hsc1]
        rw [one_mul]
        exact hψone (K.e v) i
      map_mul' := by
        intro g g'
        simp only [Subgroup.coe_mul]
        rw [map_mul (resLe (Tower.F_le T)), hψmul _ _ _ (hmem v g) _ (hmem v g'), hsc, map_mul]
        ring }
    (fun g => ((hscu (g : G T.L Ω)).map (algebraMap c'.O X.B)).mul (hψunit _ _ _ (hmem v g))), ?_⟩
  intro v i g
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
theorem UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), (∃ B : W.UniversalOrdinaryDeterminantRing K.r, True) ∧ ∀ B : W.UniversalOrdinaryDeterminantRing K.r, ∃ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X n B φ := by
  intro U Ω _ _ _ l _ c D T _ _ c' h K X n
  obtain ⟨hs, hq, hk⟩ := phiKer K.V
  obtain ⟨E, hE, hcp, hc⟩ := phiDet (maximalIdeal X.B) (algebraMap X.B X.A) X.inj K.V.pr hs hq (K.rho X n) (K.cpT X n)
    (fun g => (phiCpMap K X n g).2.2.2) (phiCpCont K X n)
    fun U hU hle => hk U hU fun A v hA hv => (phiUnr K X n A v hA hv).trans hle
  obtain ⟨ψ, hψ⟩ := phiPsiEx K X n
  obtain ⟨p, hD, hp⟩ := phiPair K.r X.inj (by norm_num) K.V.pr hs (K.rho X n) E ψ hE hc
    (fun g => (congrArg _ (hcp g)).trans (phiCpRed K X n g)) (phiIsPsi K X n ψ hψ) (phiPol K X n)
    (fun v => ⟨_, rfl, phiFlag K X n ψ hψ v⟩) (phiIne K X n)
  obtain ⟨B₀⟩ := U.b0 l T.L Ω K.s K.V c' 4 K.r X.B ⟨p⟩
  refine ⟨⟨B₀, trivial⟩, fun B => ?_⟩
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := B.univ X.B p
  refine ⟨φ, fun g => ?_, fun v i g => ?_⟩
  · have e := chi_map B.u.D (φ : B.B →+* X.B) (K.V.pr g)
    rw [h1, hD] at e
    exact e.symm.trans (hcp g)
  · have e := congrArg Units.val (DFunLike.congr_fun (h2 v i) g)
    rw [hp] at e
    exact e.trans (hψ v i g)
end
end
end
