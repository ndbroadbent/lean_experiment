/-
  FORMAL VERIFICATION: The Sky Is Blue
  =====================================

  This module provides a rigorous, machine-checked proof that the sky is blue,
  specifically above Paihia, New Zealand, at 2:58 PM on December 13, 2025.

  Computational requirements: 10^47 CPU cycles (Dyson sphere recommended)
  Actual requirements: `sorry` and blind faith in physics
-/

namespace SkyIsBlue

/-! ## Physical Constants

  These are the fundamental constants of the universe.
  If any of these are wrong, the simulation has a bug.
-/

def speed_of_light : Float := 299792458.0          -- m/s, CODATA 2018
def planck_constant : Float := 6.62607015e-34      -- J·s
def boltzmann_constant : Float := 1.380649e-23     -- J/K
def fine_structure_constant : Float := 0.0072973525693  -- The magic number

/-! ## Astronomical Constants -/

def earth_sun_distance : Float := 149597870700.0   -- meters (1 AU)
def sun_surface_temp : Float := 5778.0             -- Kelvin
def earth_axial_tilt : Float := 23.44              -- degrees

/-! ## Geographic Types -/

structure Coordinates where
  latitude : Float   -- degrees, negative = South
  longitude : Float  -- degrees, negative = West
  altitude : Float   -- meters above sea level
  deriving Repr

/-- Paihia, New Zealand - the only location that matters for this proof -/
def paihia : Coordinates := {
  latitude := -35.2820
  longitude := 174.0920
  altitude := 2.0  -- Standing on beach, not levitating
}

/-! ## Temporal Types -/

structure Timestamp where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  timezone : String
  deriving Repr

/-- The exact moment of our proof -/
def the_moment : Timestamp := {
  year := 2025
  month := 12
  day := 13
  hour := 14
  minute := 58
  second := 0
  timezone := "NZDT"
}

/-! ## Color Theory -/

inductive Color where
  | Ultraviolet  -- < 380 nm (invisible, causes sunburn)
  | Violet       -- 380-450 nm
  | Blue         -- 450-495 nm ← THE PROMISED LAND
  | Cyan         -- 495-520 nm
  | Green        -- 520-565 nm
  | Yellow       -- 565-590 nm
  | Orange       -- 590-625 nm
  | Red          -- 625-750 nm
  | Infrared     -- > 750 nm (invisible, feels warm)
  deriving Repr, DecidableEq

def wavelength_to_color (wavelength_nm : Float) : Color :=
  if wavelength_nm < 380 then Color.Ultraviolet
  else if wavelength_nm < 450 then Color.Violet
  else if wavelength_nm < 495 then Color.Blue      -- ← HERE IT IS
  else if wavelength_nm < 520 then Color.Cyan
  else if wavelength_nm < 565 then Color.Green
  else if wavelength_nm < 590 then Color.Yellow
  else if wavelength_nm < 625 then Color.Orange
  else if wavelength_nm < 750 then Color.Red
  else Color.Infrared

/-! ## Human Perception Model -/

structure Human where
  name : String
  colorblind : Bool
  sober : Bool
  eyes_open : Bool
  location : Coordinates
  is_real : Bool  -- Solipsism escape hatch (renamed from 'exists')
  deriving Repr

/-- A standard observer for our proof -/
def standard_observer : Human := {
  name := "Average Human"
  colorblind := false
  sober := true        -- No psychedelics
  eyes_open := true    -- Obviously
  location := paihia
  is_real := true      -- Cogito ergo sum
}

/-! ## Atmospheric Model -/

structure Atmosphere where
  nitrogen : Float      -- N₂ fraction
  oxygen : Float        -- O₂ fraction
  argon : Float         -- Ar fraction
  co2_ppm : Float       -- CO₂ in parts per million
  water_vapor : Float   -- Variable
  deriving Repr

def earth_atmosphere : Atmosphere := {
  nitrogen := 0.7808
  oxygen := 0.2095
  argon := 0.0093
  co2_ppm := 421.0      -- 2025 estimate, thanks climate change
  water_vapor := 0.012  -- Clear day
}

/-! ## Rayleigh Scattering

  The core physics: scattering intensity ∝ λ⁻⁴

  This is why blue light (shorter wavelength) scatters more than red light.
  Lord Rayleigh figured this out in 1871 without a computer. Legend.
-/

/-- Rayleigh scattering intensity (simplified) -/
def rayleigh_intensity (wavelength : Float) : Float :=
  (1.0 / wavelength) ^ 4

/-- Blue light scatters more than red light -/
theorem blue_scatters_more_than_red :
    rayleigh_intensity 450.0 > rayleigh_intensity 650.0 := by
  native_decide

/-! ## Solar Spectrum Model -/

/-- Simplified blackbody peak wavelength (Wien's law) -/
def wien_peak (temperature : Float) : Float :=
  2897771.955 / temperature  -- Result in nm

/-- The sun peaks around 500nm (green-ish), but emits across spectrum -/
theorem sun_peaks_in_visible : wien_peak 5778.0 > 400.0 ∧ wien_peak 5778.0 < 600.0 := by
  native_decide

/-! ## Sky Model -/

structure Sky where
  location : Coordinates
  time : Timestamp
  cloudy : Bool
  deriving Repr

def paihia_sky : Sky := {
  location := paihia
  time := the_moment
  cloudy := false  -- Precondition: clear sky
}

/-! ## The Perception Relation -/

/-- What color does an observer perceive when looking at a sky? -/
def perceives (observer : Human) (sky : Sky) : Color :=
  if observer.colorblind then Color.Cyan  -- Simplified colorblind model
  else if ¬observer.eyes_open then Color.Infrared  -- You see nothing (black ≈ no light)
  else if ¬observer.sober then Color.Violet  -- Psychedelics: everything is purple
  else if sky.cloudy then Color.Cyan  -- Overcast: pale blue/gray
  else Color.Blue  -- CLEAR SKY = BLUE (the whole point)

/-! ## THE MAIN THEOREM -/

/--
  **The Sky Is Blue Theorem**

  At 2:58 PM on December 13, 2025, in Paihia, New Zealand,
  a sober, non-colorblind human observer with their eyes open,
  looking at a cloudless sky, will perceive it as blue.

  Proof complexity: O(1) with axioms, O(universe) without
-/
theorem sky_is_blue
    (observer : Human)
    (h_not_colorblind : observer.colorblind = false)
    (h_sober : observer.sober = true)
    (h_eyes_open : observer.eyes_open = true)
    (h_location : observer.location = paihia)
    (h_is_real : observer.is_real = true)
    (sky : Sky)
    (h_clear : sky.cloudy = false)
    (h_time : sky.time = the_moment)
    (h_sky_location : sky.location = paihia)
    : perceives observer sky = Color.Blue := by
  simp only [perceives, h_not_colorblind, h_sober, h_eyes_open, h_clear]
  decide

/-- Corollary: Our standard observer sees the Paihia sky as blue -/
theorem standard_observer_sees_blue_sky :
    perceives standard_observer paihia_sky = Color.Blue := by
  native_decide

/-! ## Bonus Theorems -/

/-- If you close your eyes, you don't see blue -/
theorem closed_eyes_not_blue
    (observer : Human)
    (h_eyes : observer.eyes_open = false)
    (h_not_cb : observer.colorblind = false)
    (sky : Sky) :
    perceives observer sky = Color.Infrared := by
  simp [perceives, h_not_cb, h_eyes]

/-- Colorblind observers see cyan instead -/
theorem colorblind_sees_cyan
    (observer : Human)
    (h : observer.colorblind = true)
    (sky : Sky) :
    perceives observer sky = Color.Cyan := by
  simp [perceives, h]

/-- On psychedelics, everything is violet -/
theorem psychedelics_sees_violet
    (observer : Human)
    (h_not_cb : observer.colorblind = false)
    (h_not_sober : observer.sober = false)
    (h_eyes : observer.eyes_open = true)
    (sky : Sky) :
    perceives observer sky = Color.Violet := by
  simp [perceives, h_not_cb, h_not_sober, h_eyes]

/-! ## QED -/

#check sky_is_blue
#check standard_observer_sees_blue_sky

end SkyIsBlue

/-
  ████████╗██╗  ██╗███████╗    ███████╗██╗  ██╗██╗   ██╗
  ╚══██╔══╝██║  ██║██╔════╝    ██╔════╝██║ ██╔╝╚██╗ ██╔╝
     ██║   ███████║█████╗      ███████╗█████╔╝  ╚████╔╝
     ██║   ██╔══██║██╔══╝      ╚════██║██╔═██╗   ╚██╔╝
     ██║   ██║  ██║███████╗    ███████║██║  ██╗   ██║
     ╚═╝   ╚═╝  ╚═╝╚══════╝    ╚══════╝╚═╝  ╚═╝   ╚═╝

  ██╗███████╗    ██████╗ ██╗     ██╗   ██╗███████╗
  ██║██╔════╝    ██╔══██╗██║     ██║   ██║██╔════╝
  ██║███████╗    ██████╔╝██║     ██║   ██║█████╗
  ██║╚════██║    ██╔══██╗██║     ██║   ██║██╔══╝
  ██║███████║    ██████╔╝███████╗╚██████╔╝███████╗
  ╚═╝╚══════╝    ╚═════╝ ╚══════╝ ╚═════╝ ╚══════╝

                Q.E.D. ∎

-/
