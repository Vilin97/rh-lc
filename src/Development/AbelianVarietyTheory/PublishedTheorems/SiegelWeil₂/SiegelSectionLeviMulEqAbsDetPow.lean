module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RegSch

namespace GlobalTheory.Published.SiegelSectionIwasawa

variable {D : D7}

private theorem isFullLattice_of_good {V : HSp D} {l : Lvl V} (hl : l.Good) :
    Submodule.IsFullLattice D.host.E l.L := by
  refine { toIsLattice := hl.1, span_eq_top := ?_ }
  by_contra hspan
  obtain ⟨f, hf₀, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨v, _⟩ := exists_split_place (isCMExt_host D)
  let A : Matrix (Fin 1) (Fin V.rank) D.host.E := Matrix.of fun _ j => f (Pi.single j 1)
  have hA (x : Fin V.rank → D.host.E) : (A *ᵥ x) 0 = f x := by
    conv_rhs => rw [pi_eq_sum_univ' x]
    simp [A, Matrix.mulVec, dotProduct, mul_comm]
  have hker {y} (hy : y ∈ latLoc D.host.F l.L v) :
      (A.map (inclR (Fv D.host.F v)) *ᵥ y) 0 = 0 := by
    refine latLoc_induction (p := fun z => (A.map (inclR (Fv D.host.F v)) *ᵥ z) 0 = 0)
      (fun a _ x hx => ?_) (by simp) (fun x y hx hy => by simp [Matrix.mulVec_add, hx, hy])
      (fun x hx => by simp [Matrix.mulVec_neg, hx]) hy
    have e : (A.map (inclR (Fv D.host.F v)) *ᵥ (fun i => a ⊗ₜ[D.host.F] x i)) 0 =
        a ⊗ₜ[D.host.F] (A *ᵥ x) 0 := by
      simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]
    rw [e, hA, LinearMap.mem_ker.mp (hf (Submodule.subset_span hx)), TensorProduct.tmul_zero]
  -- The dual of any full lattice containing the level lattice lies in its local dual.
  let M := l.L ⊔ frameLat V
  let := SelfDual.isLattice_frameLat V
  have hM : Submodule.IsFullLattice D.host.E M :=
    Submodule.IsFullLattice.of_le_of_fg D.host.E le_sup_right
      (hl.1.fg.sup (SelfDual.isLattice_frameLat V).fg)
  have hLM : l.L ≤ M := le_sup_left
  have hle : latLoc D.host.F l.L v ≤ latLoc D.host.F M v := fun _ hy =>
    latLoc_induction (p := fun z => z ∈ latLoc D.host.F M v)
      (fun _ ha _ hx => tmul_mem_latLoc ha (hLM hx)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hdet := (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  have hdual := SelfDual.isLattice_dualGlob (σ := D.sp.cm.sig) hdet hM
  apply hf₀
  apply LinearMap.ext_on hdual.span_eq_top
  intro y hy
  change f y = 0
  have hmem := tmul_mem_latLoc (v := v) (one_mem _) hy
  rw [SelfDual.latLoc_dualGlob hdet hM] at hmem
  have hy' : (fun i => inclR (Fv D.host.F v) (y i)) ∈ latLoc D.host.F l.L v := by
    rw [hl.2.1 v]
    exact fun z hz => hmem z (hle hz)
  have hzero := hker hy'
  rw [SelfDual.map_mulVec_inclR, hA, ← map_zero (inclR (Fv D.host.F v))] at hzero
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (Fv D.host.F v)).injective hzero

def relat (V : HSp D) (l : Lvl V) (hl : l.Good) : HSp D :=
  { V with
    L0 := l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
    standardTuple_isLattice := by
      have e : l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)) =
          l.L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
        ext x
        constructor
        · intro hx; exact ⟨_, hx, V.frame.equivFun.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          change V.frame.equivFun (V.frame.equivFun.symm y) ∈ l.L
          rwa [LinearEquiv.apply_symm_apply]
      rw [e]
      exact Submodule.IsLattice.of_fg D.host.E (hl.1.fg.map _)
    baseLattice_isUnimodular := by
      have h := (SelfDual.forall_isSelfDualAt_iff
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
        (isFullLattice_of_good hl)).1 hl.2.1
      have e : ∀ x y, hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := fun x y => by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
        simp only [← Module.Basis.equivFun_apply]
        rfl
      ext z
      have h2 : z ∈ Formalism.HermitianLatticesTheory.dual V.hT (l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
          ∀ x ∈ l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)),
            V.hT x z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
      refine h2.trans (Iff.trans ?_ (h (V.frame.equivFun z)).symm)
      constructor
      · intro H x hx
        obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
        rw [e]
        exact Submodule.mem_one.1 (H x hx)
      · intro H x hx
        rw [← e]
        exact Submodule.mem_one.2 (H _ hx) }

theorem frameLat_relat (V : HSp D) (l : Lvl V) (hl : l.Good) : frameLat (relat V l hl) = l.L := by
  ext y
  exact iff_of_eq (congrArg (· ∈ l.L) (V.frame.equivFun.apply_symm_apply y))

theorem hasIw_of_good {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) : HasIw d l.K := by
  let d' : HypDec (relat V l hl) V₀ r := ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩
  have h := GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D (relat V l hl) V₀ r d' l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2
  intro g
  obtain ⟨q, k, hk, e⟩ := h g
  have e2 : (Kmax (relat V l hl) l.c : Subgroup (GA D V)) = l.K :=
    congrArg (fun L => levelAll D.sp.cm.sig V.gram L l.c) (frameLat_relat V l hl)
  exact ⟨⟨q.1, q.2⟩, k, e2 ▸ hk, e⟩

section Arch

variable {m k r : ℕ} {X Y : Matrix (Fin m) (Fin r) ℂ} {Z : Matrix (Fin m) (Fin k) ℂ} {P R : Matrix (Fin r) (Fin m) ℂ}
  {Q : Matrix (Fin k) (Fin m) ℂ} {G : Matrix (Fin m) (Fin m) ℂ} {G₀ s₀ B B' : Matrix (Fin k) (Fin k) ℂ}

end Arch

section Standard

variable {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r)

variable {L₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}

end Standard

end GlobalTheory.Published.SiegelSectionIwasawa

end
