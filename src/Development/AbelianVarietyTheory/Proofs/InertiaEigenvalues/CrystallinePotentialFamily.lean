module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Mathlib.RingTheory.Localization.Module
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplementedSubrepLocalMatrixRepTwistedSumStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairing

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual




theorem exists_dualLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ hO hcyc U U' P hP LT

  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hfr
  haveI : Module.Finite O LT.T := Module.Finite.iff_fg.mpr LT.fg
  haveI : Module.Free O LT.T := LT.free
  let b := Module.Free.chooseBasis O LT.T
  let e : Module.Free.ChooseBasisIndex O LT.T → U.V := fun i => (b i : U.V)
  have he_O : LinearIndependent O e := b.linearIndependent.map' LT.T.subtype (Submodule.ker_subtype _)
  have he_L : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).mp he_O
  have hspanO : Submodule.span O (Set.range e) = LT.T := by
    have h1 : Set.range e = LT.T.subtype '' Set.range b := (Set.range_comp _ _)
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanL : Submodule.span LL (Set.range e) = ⊤ := by
    rw [← Submodule.span_span_of_tower O LL (Set.range e), hspanO]; exact LT.span
  let bL := Basis.mk he_L (le_of_eq hspanL.symm)
  have hbL : ∀ i, bL i = e i := fun i => Basis.mk_apply _ _ _
  let φ : U'.V →ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearMap.pi (fun i => P (e i))
  have hφ : ∀ y i, φ y i = P (e i) y := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hP.2.2.1 y
    intro x
    have h1 : P.flip y = 0 := bL.ext (fun i => by
      rw [hbL]; simpa [hφ] using congrFun hy i)
    simpa using LinearMap.congr_fun h1 x
  have hdim : finrank LL U'.V = finrank LL (Module.Free.ChooseBasisIndex O LT.T → LL) := by
    rw [← hP.2.2.2, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis bL]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφinj
  let φe : U'.V ≃ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let bf := (Pi.basisFun LL (Module.Free.ChooseBasisIndex O LT.T)).map φe.symm
  have hφf : ∀ i j, P (e j) (bf i) = (Pi.single i (1 : LL) : Module.Free.ChooseBasisIndex O LT.T → LL) j := fun i j => by
    have : φ (bf i) = Pi.single i 1 := by
      simp only [bf, Basis.map_apply, Pi.basisFun_apply]
      exact φe.apply_symm_apply _
    exact congrFun this j
  let T' : Submodule O U'.V :=
    { carrier := {y | ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a}
      add_mem' := by
        intro y z hy hz x hx
        obtain ⟨a, ha⟩ := hy x hx
        obtain ⟨c, hc⟩ := hz x hx
        exact ⟨a + c, by simp [ha, hc]⟩
      zero_mem' := fun x _ => ⟨0, by simp⟩
      smul_mem' := by
        intro c y hy x hx
        obtain ⟨a, ha⟩ := hy x hx
        refine ⟨c * a, ?_⟩
        show P x (c • y) = _
        rw [← algebraMap_smul LL c y, map_smul, ha, smul_eq_mul, map_mul] }
  have hmem : ∀ y, y ∈ T' ↔ ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a := fun y => Iff.rfl
  have hmem' : ∀ y, y ∈ T' ↔ ∀ i, P (e i) y ∈ Set.range (algebraMap O LL) := by
    intro y; constructor
    · intro hy i; obtain ⟨a, ha⟩ := hy (e i) (b i).2; exact ⟨a, ha.symm⟩
    · intro hy x hx
      choose a ha using hy
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • e i := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h2
        exact h2.symm
      obtain ⟨c, hcx⟩ : ∃ c : Module.Free.ChooseBasisIndex O LT.T → O, x = ∑ i, c i • e i := ⟨_, hx'⟩
      refine ⟨∑ i, c i * a i, ?_⟩

      rw [hcx, map_sum, LinearMap.sum_apply, map_sum (algebraMap O LL)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← algebraMap_smul LL (c i) (e i), map_smul, LinearMap.smul_apply, ← ha i,
        smul_eq_mul, map_mul]
  have hf_mem : ∀ i, bf i ∈ T' := fun i => (hmem' _).mpr fun j => by
    rw [hφf]
    refine ⟨(Pi.single i (1 : O) : Module.Free.ChooseBasisIndex O LT.T → O) j, ?_⟩
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  have hT'eq : T' = Submodule.span O (Set.range bf) := by
    apply le_antisymm
    · intro y hy
      choose a ha using (hmem' y).mp hy
      have hy' : y = ∑ i, a i • bf i := by
        apply hφinj
        funext j

        rw [hφ, hφ, map_sum, ← ha j]
        simp_rw [← algebraMap_smul LL (a _) (bf _), map_smul, hφf, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        simp
      rw [hy']
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hf_mem i
  have hfO : LinearIndependent O bf := (LinearIndependent.iff_fractionRing O LL).mpr bf.linearIndependent
  have hstab : ∀ g, ∀ y ∈ T', U'.ρ g y ∈ T' := by
    intro g y hy x hx
    obtain ⟨u, hu⟩ := hcyc g
    obtain ⟨a, ha⟩ := hy (U.ρ g⁻¹ x) (LT.stable g⁻¹ x hx)
    refine ⟨u * a, ?_⟩
    have hx' : U.ρ g (U.ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h3 := hP.1 g (U.ρ g⁻¹ x) y
    rw [hx'] at h3
    rw [h3, hu, ha, map_mul]
  have hopenT : IsOpen (T' : Set U'.V) := by
    have h4 : (T' : Set U'.V) = ⋂ i, (fun y => P (e i) y) ⁻¹' Set.range (algebraMap O LL) := by
      ext y; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact hmem' y
    rw [h4]
    exact isOpen_iInter_of_finite
      (fun i => hopen.preimage (IsModuleTopology.continuous_of_linearMap (R := LL) (P (e i))))
  refine ⟨⟨T', hstab, ?_, ?_, ?_⟩, ⟨hP, hmem⟩, hopenT⟩
  · rw [hT'eq]; exact Submodule.fg_span (Set.finite_range _)
  · rw [hT'eq]; exact Module.Free.of_basis (Basis.span hfO)
  · rw [hT'eq, Submodule.span_span_of_tower O LL]; exact bf.span_eq

end GlobalTheory.Pass.LocDual

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairingStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  first | exact @GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | exact GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | (intros; apply GlobalTheory.Pass.LocDual.exists_dualLat_isOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRham

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDualDR




theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  intro D hFont hP i r hr Xs w hw n hPot X hX X' PX hD
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  obtain ⟨h1, h2, h3, h4⟩ := hD
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X'.V, ρ := X'.ρ.comp incl, cont := fun v => (X'.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW : IsCrys ((D.loc (D.nd.l i)).PD K') W.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W) (hA := hsub)).1
  have hcyc : ∀ g : ↥(GK K'),
      ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
        ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) (incl g) : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
    intro g
    have e1 := (D.loc (D.nd.l i)).PD_χ K' g
    have e2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (incl g)
    change algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((((D.loc (D.nd.l i)).PD K').χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (incl g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i])
    rw [e1, e2]
    rfl
  have hD' : IsDual1 ((D.loc (D.nd.l i)).PD K') W.ρ W'.ρ PX := by
    refine ⟨fun g v y => ?_, h2, h3, h4⟩
    rw [hcyc]
    exact h1 (incl g) v y
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (hFont (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1 W W' PX hD' hW
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X' hW'

end GlobalTheory.SummandDualDR

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRhamStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.tateDual_twistedSumSummand_isDeRham : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  first | exact @GlobalTheory.SummandDualDR.main | exact GlobalTheory.SummandDualDR.main | (intros; apply GlobalTheory.SummandDualDR.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamily

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDualU

theorem dualLatLe_of {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] [IsDomain O] [IsFractionRing O LL]
    (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT' : Lattice (O := O) U'.ρ) (hLT' : IsDualLat1 PD LT LT' P) (hopen : IsOpen (LT'.T : Set U'.V)) (b : ℕ)
    (h : finrank LL (FiniteCohomology PD U'.ρ) + finrank O ↥LT.T ≤ b) : DualLatLe PD U U' LT P b :=
  ⟨LT', hLT', by rw [GlobalTheory.TopSteps.FinSummand.finrank_h1fT PD LT' hopen]; exact h⟩


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  intro D hF hDR hBK i r hR Xs w hw hK n hPot k M hSub
  have hSum := GlobalTheory.T.isComplementedSubrep_localMatrixRep_twistedSum D i r hR Xs w hw k M hSub
  obtain ⟨hU, X', PX, hD1, hSF⟩ := GlobalTheory.T.potential_family_summand_restriction D hF hDR i r hR Xs w hw n hPot _ hSum
  have hX' := GlobalTheory.T.tateDual_twistedSumSummand_isDeRham D hF hDR i r hR Xs w hw n hPot _ hSum X' PX hD1
  have hGood := goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL
  have hcyc : ∀ g, ∃ u : (Br.OLL D.nbr i w hw)ˣ, ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :
      (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) (u : Br.OLL D.nbr i w hw) := by
    intro g
    rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
    exact ⟨Units.map (D.nbr i w hw).eO.toRingHom.toMonoidHom (epsU D.nd i ((decS D.nd w) (Br.iota D.nbr i w hw g))), rfl⟩
  obtain ⟨LT', hLT', hopen⟩ := GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing (Br.PD D.loc D.nbr i w hw) hGood hcyc _ X' PX hD1
    (Br.locLat D.nbr i w hw M)
  refine ⟨hU, X', PX, hSF, ?_⟩
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hGood
  haveI := hdom
  haveI := hfr
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  refine dualLatLe_of _ _ X' _ PX LT' hLT' hopen _ ?_
  have h2 := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL hK
    (hBK (D.nd.l i) (D.nbr i w hw).Kw) X' hX'
  have h3 : finrank (Br.LL D.nbr i w hw) X'.V = k := by
    rw [← hD1.2.2.2]
    exact Module.finrank_fin_fun _
  have h4 : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
    have e := LinearEquiv.ofInjective _ (stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k)
    exact (LinearEquiv.finrank_eq e).symm.trans (Module.finrank_fin_fun _)
  have h5 : finrank (Br.LL D.nbr i w hw) (FiniteCohomology (Br.PD D.loc D.nbr i w hw) X'.ρ) ≤ k := h3 ▸ h2
  exact le_trans (Nat.add_le_add h5 h4.le) (by omega)

end GlobalTheory.Pass.LocDualU

end
end
end
