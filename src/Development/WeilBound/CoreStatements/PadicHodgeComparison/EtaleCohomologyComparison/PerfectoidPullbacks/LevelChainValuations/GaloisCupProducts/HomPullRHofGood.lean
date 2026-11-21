module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homPull_good_of_nmHM_pull
    (hr : ∀ n j x, nmHM (nmPullA L u hu) l s none n j (rHN n j x) =
      rHM n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x)) :
    (homPull hL u hu s hQN hQM rHN rHM).Good := by
  exact
    { ℓ := rfl
      lam _ := rfl
      ι _ := rfl
      o _ := rfl
      tS n j x := ((Model.pullH u hu false j).comm n x).symm
      r n j x := hr n j x
      red n j z := nmHM_redM _ l s none n j z
      b j z := nmHO_nmPullB_bMap hL u hu s hQN hQM j z
      μ j v := by
        have hμ :
            nmHO (nmPullB L u hu) 1 s j (muB L.γB N.q 1 s {⊤} j v) =
              muB L.γB M.q 1 s {⊤} j (pullR j (Model.genMap u hu) (Model.genMap_q u hu) v) := by
          let restrictN := CH.Mor.restrict (O (smFun N.gen N.q)) (TO N.q 1 s {⊤}).ι
          let restrictM := CH.Mor.restrict (O (smFun M.gen M.q)) (TO M.q 1 s {⊤}).ι
          let changeN := (smO L.γB N.q 1 s {⊤}).o
          let changeM := (smO L.γB M.q 1 s {⊤}).o
          let pullB := (nmS (nmPullB L u hu) 1 s).o
          let pullK : CH.Mor (O (smFun N.gen N.q)) (O (smFun M.gen M.q)) (RingHom.id K) :=
            ⟨(smMor (Model.genMap u hu) (Model.genMap_q u hu)).functor,
              fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
              fun _ _ => rfl⟩
          let left := (restrictN.comp (σ'' := algebraMap K L.B) changeN).comp
            (σ'' := algebraMap K L.B) pullB
          let right := (pullK.comp (σ'' := RingHom.id K) restrictM).comp
            (σ'' := algebraMap K L.B) changeM
          let η : left.G ⟶ right.G :=
            { app := fun T => LevelPullbackIdentities.thHom (L := smFun N.gen N.q)
                ⟨fun i => Empty.elim i⟩ rfl (RingHom.id T.obj.B) (fun _ => rfl)
                (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h) (by
                  refine Subtype.ext (Prod.ext ?_ ?_)
                  · exact Ideal.Quotient.ringHom_ext
                      (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _)
                  · refine (LevelPullbackIdentities.spec_qid _ (fun _ h => h) _).trans ?_
                    change (T.obj.y.1.2 ≫ Model.genMap u hu) ≫ 𝟙 N.gen =
                      (T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ Model.genMap u hu
                    simp)
              naturality := fun _ _ _ =>
                Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun i => Empty.elim i) }
          have hN := CrystallineSemistableComparison.pull_pull (algebraMap K L.B)
            restrictN changeN j v
          have hLeft := CrystallineSemistableComparison.pull_pull (algebraMap K L.B)
            (restrictN.comp (σ'' := algebraMap K L.B) changeN) pullB j v
          have hM := CrystallineSemistableComparison.pull_pull (RingHom.id K)
            pullK restrictM j v
          have hRight := CrystallineSemistableComparison.pull_pull (algebraMap K L.B)
            (pullK.comp (σ'' := RingHom.id K) restrictM) changeM j v
          have hη := CrystallineSemistableComparison.P.prism left right η (fun _ _ => rfl) j v
          exact (congrArg (pullB.pull j) hN).trans
            (hLeft.trans (hη.trans (hRight.symm.trans (congrArg (changeM.pull j) hM.symm))))
        exact hμ }

end

theorem homPull_rHof_good {m : ℕ} {L : Lev (per l K) m}
    (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
    {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ) (hL : L.Good)
    (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
    (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (homPull hL u hu s hQN hQM (rHof d hc N s) (rHof d hc M s)).Good :=
  homPull_good_of_nmHM_pull hL u hu s hQN hQM _ _ (rHof_pull d hc u hu s)

end CrystallineSemistableComparison.Pb.Kap
