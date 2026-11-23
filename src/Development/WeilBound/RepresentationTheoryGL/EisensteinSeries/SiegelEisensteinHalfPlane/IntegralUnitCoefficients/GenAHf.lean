module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.IsIntUnit
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockLowerRightMulBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
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
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenUnit
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenUnit
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.MaxSurjInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SiegelParabolicUnnMatrixBlockUpperTriangular

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFin

section

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinH

variable {n : ℕ}

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (blkDm M).map f = blkDm (M.map f) := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  unfold blkDm
  rw [Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

theorem det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

end PositivityTheory.Rg.Sw.Glob.GenFinH

namespace PositivityTheory.Rg.Sw.Glob

open GenFinH

theorem kInFin_of (hU : UnitD) (hL : LocFin) (hGL : GlueLevi) (hGW : GlueW) (hUA : UnitAE) : KInFin := by
  intro D n k hk hreal
  choose a I hgood using fun v => hL D n k hk v
  obtain ⟨m, hm, hmv, hmr⟩ := hGL D n a (fun v => (hgood v).1) (fun v => (hgood v).2.1)
  obtain ⟨w, hw, hwv, hwr⟩ := hGW D n I
  have hmat : ∀ {S : Type} [CommRing S] (f : AE D →+* S), (mat (k * m * w)).map f = (mat k).map f * (mat m).map f * (mat w).map f := by
    intro S _ f
    show (mat k * mat m * mat w).map f = _
    rw [Matrix.map_mul, Matrix.map_mul]
  have hd : IsUnit (blkDm (mat (k * m * w))).det := by
    apply hUA D
    · intro τ
      rw [det_map, blkDm_map, hmat, hreal τ, hmr τ, hwr τ, Matrix.mul_one, Matrix.mul_one, blkDm_one, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [det_map, blkDm_map, hmat, hmv v, hwv v]
      exact (hgood v).2.2
  have h1 : k * m * w ∈ Subgroup.closure (genSet D n) := hU D n _ hd
  have hm' : m ∈ Subgroup.closure (genSet D n) := Subgroup.subset_closure hm
  have e : k = k * m * w * w⁻¹ * m⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hm')

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenGlue

section

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace PositivityTheory.Rg.Sw.Glob.GenGlueH

variable {D : D7} {n : ℕ}

theorem compAt_sigR (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig z) =
      sigR (Fv D.host.F v) D.sp.cm.sig (GlobalTheory.FinPl.compAt D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem glueFull (f : D.what₂.Tau → ℂ) (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v)
    (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = f τ) ∧ ∀ v, GlobalTheory.FinPl.compAt D v x = z v := by
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z hz
  refine ⟨Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D f) (finPart D s),
    fun τ => Formalism.IndefR.Eqv.psiT_glueA D τ f _, fun v => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D _) = _
  rw [Formalism.IndefR.Eqv.finPart_glueA]
  exact hs v

theorem map_inv_of {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : (M⁻¹).map f = (M.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem adj_map {S : Type} [CommRing S] (f : AE D →+* S) (σS : S →+* S)
    (hf : ∀ z, f (sigR (AF D.host.F) D.sp.cm.sig z) = σS (f z)) (x : Matrix (Fin n) (Fin n) (AE D)) :
    (GlobalTheory.MixModel.adj x).map f = ((x.map f).map σS)ᵀ := by
  ext i j
  simp only [GlobalTheory.MixModel.adj, Matrix.map_apply, Matrix.transpose_apply]
  exact hf _

theorem isUnit_of_intUnit {v : GlobalTheory.FinPl.Pl D} {z : Ev D v} (h : IsIntUnit z) : IsUnit z := by
  obtain ⟨-, z', -, hz⟩ := h
  exact ⟨⟨z, z', hz, by rw [mul_comm]; exact hz⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.GenGlueH

namespace PositivityTheory.Rg.Sw.Glob

open GenGlueH

theorem glueLevi : GlueLevi := by
  intro D n a hint hdet
  have hE : ∀ i j, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = (1 : Matrix (Fin n) (Fin n) ℂ) i j) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = a v i j := fun i j => glueFull _ (fun v => a v i j) (fun v => hint v i j)
  choose A hAτ hAv using hE
  let A' : Matrix (Fin n) (Fin n) (AE D) := Matrix.of A
  have hτ : ∀ τ, A'.map (Formalism.IndefR.Eqv.psiT D τ) = 1 := fun τ => by ext i j; exact hAτ i j τ
  have hv : ∀ v, A'.map (GlobalTheory.FinPl.compAt D v) = a v := fun v => by ext i j; exact hAv i j v
  have hdetA : IsUnit A'.det := by
    apply unitAE D
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hτ τ, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hv v]
      exact hdet v
  let u : GL (Fin n) (AE D) := ((Matrix.isUnit_iff_isUnit_det A').2 hdetA).unit
  have hu : (u : Matrix (Fin n) (Fin n) (AE D)) = A' := IsUnit.unit_spec _
  have hui : ((u⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = A'⁻¹ := by
    rw [Matrix.coe_units_inv, hu]
  obtain ⟨m, hm⟩ := GlobalTheory.StdUnn.Model.exists_levi u
  refine ⟨m, Or.inr (Or.inl ⟨_, _, hm⟩), fun v => ?_, fun τ => ?_⟩
  · rw [show cTv (a v) = ((a v).map (sigR (Fv D.host.F v) D.sp.cm.sig))ᵀ from rfl,
      hm, PlaceFactsH.block_matrix_map, hu, hv v, hui,
      adj_map (GlobalTheory.FinPl.compAt D v) (sigR (Fv D.host.F v) D.sp.cm.sig) (compAt_sigR v),
      map_inv_of (GlobalTheory.FinPl.compAt D v) A' hdetA, hv v,
      map_inv_of (sigR (Fv D.host.F v) D.sp.cm.sig) (a v) (isUnit_of_intUnit (hdet v)),
      Matrix.transpose_nonsing_inv, Matrix.map_zero _ (map_zero _)]
  · rw [hm, PlaceFactsH.block_matrix_map, hu, hτ τ, hui,
      adj_map (Formalism.IndefR.Eqv.psiT D τ) (starRingEnd ℂ) (fun z => Formalism.IndefR.Eqv.psiT_sigR D τ z),
      map_inv_of (Formalism.IndefR.Eqv.psiT D τ) A' hdetA, hτ τ, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
      Matrix.map_zero _ (map_zero _), PlaceFactsH.block_matrix_one]

theorem glueW : GlueW := by
  intro D n I
  have hE : ∀ i, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = 0) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = if i ∈ I v then 1 else 0 := fun i =>
    glueFull _ _ (fun v => by split_ifs; exacts [one_mem _, zero_mem _])
  choose e heτ hev using hE
  have hσe : ∀ i, sigR (AF D.host.F) D.sp.cm.sig (e i) = e i := fun i => by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [Formalism.IndefR.Eqv.psiT_sigR, heτ, map_zero]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig (e i)) = GlobalTheory.FinPl.compAt D v (e i)
      rw [compAt_sigR, hev]
      split_ifs <;> simp
  let B : Matrix (Fin n) (Fin n) (AE D) := Matrix.diagonal e
  have hB : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, B, Matrix.diagonal_apply]
    by_cases h : j = i
    · subst h; simp [hσe]
    · simp [h, Ne.symm h]
  have hB' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [GenInfH.cT_neg', hB]
  have h1 : GenInfH.nEl B hB ∈ genSet D n := Or.inl ⟨B, GenInfH.mat_nEl B hB⟩
  have h2 : GenInfH.nBarEl (-B) hB' ∈ genSet D n := Or.inr (Or.inr ⟨-B, GenInfH.mat_nBarEl _ _⟩)
  refine ⟨GenInfH.nEl B hB * GenInfH.nBarEl (-B) hB' * GenInfH.nEl B hB,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2))
      (Subgroup.subset_closure h1), fun v => ?_, fun τ => ?_⟩
  · have hBv : B.map (GlobalTheory.FinPl.compAt D v) = eI (I v) := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, eI]
      by_cases h : i = j
      · subst h; simp [hev]
      · simp [h]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBv,
      Matrix.map_neg _ (map_neg _), hBv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      GenInfH.weyl_idem _ (GenInfH.eI_mul_self _)]
    rfl
  · have hBτ : B.map (Formalism.IndefR.Eqv.psiT D τ) = 0 := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, Matrix.zero_apply]
      split_ifs <;> simp [heτ]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (Formalism.IndefR.Eqv.psiT D τ) = 1
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBτ,
      Matrix.map_neg _ (map_neg _), hBτ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      neg_zero, PlaceFactsH.block_matrix_one, Matrix.one_mul, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenTop

section

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenTopH

variable {D : D7} {n : ℕ}

theorem mat_projFin (g : G D n) : (mat g).map (finPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projFin D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

theorem mat_projInf (g : G D n) : (mat g).map (infPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projInf D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

end PositivityTheory.Rg.Sw.Glob.GenTopH

namespace PositivityTheory.Rg.Sw.Glob

theorem genA_of : UnitD → PIn → KInInf → KInFin → GenA := by
  intro _ hP hKi hKf D n
  show Subgroup.closure (genSet D n) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  refine Subgroup.mul_mem _ (hP D n p hp) ?_
  rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]
  have hk' := mem_levelAll.1 hk
  refine Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofInf]; exact one_mem _
    · rw [projArch_ofInf, projInfArch_projInf]; exact hk'.2 w
  · rw [GenTopH.mat_projFin, projFin_ofInf]; rfl
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofFin, projFinLoc_projFin]; exact hk'.1 v
    · rw [projArch_ofFin]; exact one_mem _
  · intro τ
    have e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D) := rfl
    rw [e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]
    exact Matrix.map_one _ (map_zero _) (map_one _)

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PIn

section

@[expose] public section

noncomputable section

open GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob

theorem pIn : PIn := by
  intro D n p hp
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm⟩)))
    (Subgroup.subset_closure (Or.inl ⟨b, hu⟩))

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.GenAHf

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem genA_hf : GenA :=
  genA_of unitD pIn (kInInf_of unitD locRedField)
    (kInFin_of unitD (GenFinLocHf.locFin_of locRedField locRedSplit) glueLevi glueW unitAE)

end PositivityTheory.Rg.Sw.Glob
end
end
