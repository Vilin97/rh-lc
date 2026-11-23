module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchangeStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplitStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LocMod

theorem Place.isComp_of_chrEq : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, GlobalTheory.NPin.IsComp χ s.w μw → p.IsComp c μw := by
  intro D s p hpl hpr c χ hc μw hμ
  have he : p.e * p.e = p.e := hpl.1
  have e_ι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  let j0 : s.w.adicCompletion D.host.E →* Formalism.L2.Theta.AE D :=
    { toFun := fun x => p.ι x + (1 - p.e)
      map_one' := by rw [ho, add_sub_cancel]
      map_mul' := fun x y => by
        rw [hm]
        linear_combination e_ι x + e_ι y - he }
  have hj0 : Continuous j0 := p.cont_ι.add continuous_const
  let j : (s.w.adicCompletion D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map j0
  have hj : Continuous j := by
    refine Units.continuous_iff.2 ⟨hj0.comp Units.continuous_val, ?_⟩
    have : (fun u => ((j u)⁻¹ : (Formalism.L2.Theta.AE D)ˣ).val) =
        fun u : (s.w.adicCompletion D.host.E)ˣ => j0 ((u⁻¹ : (s.w.adicCompletion D.host.E)ˣ) : s.w.adicCompletion D.host.E) := by
      funext u; rw [← map_inv]; rfl
    rw [this]
    exact hj0.comp Units.continuous_coe_inv
  have hcc : Continuous c := hc.1.1
  have hF2 : Continuous fun u => ((c (j u) : Circle) : ℂ) := (continuous_subtype_val.comp hcc).comp hj
  have hμc : Continuous μw := by
    refine continuous_of_continuousAt_one μw ?_
    have hker : (μw.ker : Set (s.w.adicCompletion D.host.E)ˣ) ∈ nhds 1 := hμ.1.mem_nhds (by simp)
    have : (fun _ => (1 : ℂˣ)) =ᶠ[nhds 1] μw := Filter.mem_of_superset hker fun x hx => (MonoidHom.mem_ker.1 hx).symm
    have h2 := (continuousAt_const.congr this).tendsto
    rw [map_one] at h2
    rw [ContinuousAt, map_one]
    exact h2
  have hF1 : Continuous fun u => ((μw u : ℂˣ) : ℂ) := Units.continuous_val.comp hμc
  have hd : Dense (Set.range (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E))) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨u, hu⟩
    have hoe : Topology.IsOpenEmbedding (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) :=
      { toIsEmbedding := Units.isEmbedding_val₀
        isOpen_range := by
          have : Set.range (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) = {0}ᶜ := by
            ext y
            exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 y h, rfl⟩⟩
          rw [this]; exact isOpen_compl_singleton }
    obtain ⟨y, hy⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := D.host.E) s.w).exists_mem_open
      (hoe.isOpenMap U hU) ⟨u, u, hu, rfl⟩
    obtain ⟨v, hv, hvy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hvy)
    refine ⟨v, hv, Units.mk0 y hy0, Units.ext ?_⟩
    simpa using hvy.symm
  have key : ∀ x : D.host.Eˣ, ((μw (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x) : ℂˣ) : ℂ)
      = ((c (j (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x)) : Circle) : ℂ) := by
    intro x
    refine (congrArg Units.val (hμ.2 x)).trans (hc.2 s.w p.e hpl x _ ?_).symm
    change p.ι (algebraMap D.host.E (s.w.adicCompletion D.host.E) x) + (1 - p.e) = _
    rw [← hpr, GlobalTheory.LocMod.Place.pr, p.ι_π, Formalism.L2.JoinChr.locE]
    ring
  have heq := Continuous.ext_on hd hF1 hF2 (by rintro _ ⟨x, rfl⟩; exact key x)
  intro x a ha
  have hja : j x = a := Units.ext ha.symm
  rw [← hja]
  exact congrFun heq x

end GlobalTheory.LocMod
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreementStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localComponent_of_idelicCharacterAgreement : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, IsComp χ s.w μw → p.IsComp c μw := by
  first | exact @GlobalTheory.LocMod.Place.isComp_of_chrEq | exact GlobalTheory.LocMod.Place.isComp_of_chrEq | (intros; apply GlobalTheory.LocMod.Place.isComp_of_chrEq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupportedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  first | exact @GlobalTheory.PlaceSupp.idem_mul_eq_self | exact GlobalTheory.PlaceSupp.idem_mul_eq_self | (intros; apply GlobalTheory.PlaceSupp.idem_mul_eq_self <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrameRead

theorem tensCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    GlobalTheory.NJoin.tensCast h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h; rfl

theorem gen_supp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (fin : A →+* B) (Ψ : B →+* C) {m k : ℕ}
    (M : Matrix (Fin m) (Fin m) A) (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (hM : M.map fin = β * K * β') (hK : K.map Ψ = 1) : ((M - 1).map fin).map Ψ = 0 := by
  rw [Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]



theorem side_loc (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
    (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hπ : ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))))
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) :
    ∃ FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n), ∀ h, TrivOutside {s.v} h →
      p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  let Φ := c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
  refine ⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · intro i j
    apply GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported D s hF p c hπ
    · have hk := MonoidHom.mem_ker.1 (PV.into h)
      have e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
        rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
          Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
        have e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val := rfl
        rw [e3, hk, Units.val_one, sub_self]
      exact congrFun (congrFun e2 i) j
    · intro v' hv'
      have hh' := hh v' (by simpa using hv')
      have e4 := gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
        (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by
          rw [← hh']
          ext a b
          exact congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))
      exact congrFun (congrFun e4 i) j
  · have e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ :=
      Matrix.ext fun a b => hπ _
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _ := hm h
    have hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ =
        (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val := by
      refine Matrix.ext fun a b => ?_
      exact congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)
    rw [e7, e5, ← hK]
    exact (Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)

theorem main : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  intro D V W n r PV PW hF hV hW s
  obtain ⟨p, c, hId, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  have hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    unfold GlobalTheory.LocMod.Place.pr
    rw [hπ]
    have e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) =
        (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x := by
      simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
    rw [e1, tensCast_one_tmul, ← hci x]
    congr 1
    simp [ReciprocityTheory.Aut.SplitPlace.proj]
  obtain ⟨FS, hFS⟩ := side_loc D s hF p c hπ V n PV hV
  obtain ⟨FT, hFT⟩ := side_loc D s hF p c hπ W r PW hW
  exact ⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩

end GlobalTheory.SplitFrameRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  first | exact @GlobalTheory.SplitFrameRead.main | exact GlobalTheory.SplitFrameRead.main | (intros; apply GlobalTheory.SplitFrameRead.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrame

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinModSpan

theorem isComp_mul_inv {E : Type} [Field E] [NumberField E] {μ η : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {μw ηw : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsComp μ w μw) (hη : IsComp η w ηw) :
    IsComp (μ * η⁻¹) w (μw * ηw⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 := hμ.1
    have h2 := hη.1
    unfold GlobalTheory.SmGL.IsSmoothChar at h1 h2 ⊢
    have h3 : IsOpen (((μw.ker ⊓ ηw.ker : Subgroup _)) : Set (w.adicCompletion E)ˣ) := h1.inter h2
    exact Subgroup.isOpen_mono (H₁ := μw.ker ⊓ ηw.ker) (fun y hy => by
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hy ⊢
      simp [hy.1, hy.2]) h3
  · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hη.2 x]
    rfl

theorem main : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  intro D ψ V W n r PV PW hF hV hW χV χW om hom μ η hμ hη s μw ηw hμw hηw f hf
  obtain ⟨p, hpe, hpr, FS, FT, c, hc, hci, hlocV, hlocW⟩ := GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup D V W n r PV PW hF hV hW s
  have cV := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χV μ hμ μw hμw
  have cW := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χW (μ * η⁻¹) hη (μw * ηw⁻¹) (isComp_mul_inv hμw hηw)
  obtain ⟨τ, hτ, hτom⟩ := GlobalTheory.T.linearModel_fourier_transform_exchange (s.w.adicCompletion D.host.E) n r
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have h2 := GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split D _ p (Fin r) (Fin n) V W FS FT ψ hom.std f hf
  refine (iSup₂_le fun Tm hTm => ?_ : (⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm) ≤ _) h2
  have hr : LinearMap.range Tm = LinearMap.range (Tm ∘ₗ τ) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hτ, Submodule.map_top]
  rw [hr]
  refine le_iSup₂_of_le (f := fun (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)) => LinearMap.range ι) (Tm ∘ₗ τ) ⟨?_, fun Φ => hTm.theta _⟩ le_rfl
  refine ⟨c, hc, hci, fun h g hh hg Φ Φ' hΦ => ?_⟩
  have hΦ'' : Φ'.1 = GlobalTheory.SplitWeil.om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ.1 := hΦ
  have key := hOm (s.w.adicCompletion D.host.E) p ψ V W χV χW om hom μw (μw * ηw⁻¹) cV cW (Fin r) (Fin n) FS FT Tm hTm
    (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g))
    (hlocV h hh) (hlocW g hg) (τ Φ)
    (((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • τ Φ') (by
      rw [Submodule.coe_smul, hτom μw _ _ Φ Φ' hΦ'']
      congr 2
      simp [mul_inv_rev, mul_comm])
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  show om (PV.ψ h, PW.ψ g) (Tm (τ Φ)) = _
  rw [key, map_smul]

end GlobalTheory.LinModSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  first | exact @GlobalTheory.LinModSpan.main | exact GlobalTheory.LinModSpan.main | (intros; apply GlobalTheory.LinModSpan.main <;> assumption)
end
end
