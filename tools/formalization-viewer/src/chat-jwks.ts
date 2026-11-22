// Public verification keys from https://auth.openai.com/.well-known/jwks.json
// Refresh with python3 tools/update_viewer_chat_jwks.py.
export const OPENAI_JWKS = [
  {
    kty: "RSA",
    kid: "qAgbfguRn1QO32qNOWHKNrFKMOwSew1TamFZPCI78HQ",
    use: "sig",
    alg: "RS256",
    n: "xYNYiGEZikcuWUbwx0gQbjhupTZtvy_EntH-EEGio3sMZMJmSHo92j1XKTSVdHCAOj7A1tLaEG3AFQ_34Bdrlq4kgAJBXggEesNCFq4KmgTiQNtsusIyG3oo8B7Z3-inPuaR-kJwTmfrKob9euhXzj6Qf5mEzL5hkbqrDyQPdIg8jZSajeKdsPHt2YOjy6eGd4kI1sgZplpxU2wyTRmayfXkMjPLDvFX7_8yu0G7axTTjeGzyyS-8uCOWw5E2Q_Jzxp8G3Nsuug73eazaYr1zhU7FENYgMm29VrDx1PCfKRsPrbBfkfMbnzKqmzfFBSJSfDJgnDFeymZFg03WEY8uQ",
    e: "AQAB",
  },
  {
    kty: "RSA",
    kid: "SltYPghZ7R5RAGg34zm4x__sAkW02weWOKzHYBskY6E",
    use: "sig",
    alg: "RS256",
    n: "vvTdkMd0ri_9Dy7FIe7_u0Ay2qt3dA8rQz6UzEsdU-r9nMIWzVdDYrbMlsRxIZ8Cp382ymPLaIn0uY0Jc5mO3PhiFyp9jk37Cdxx9SGsDYYzXvBwToIO6RpNzr8d2ZIXmtIxA2jiTcmYhZgi7aH6v1F_Lc2Vs1nm0SvcZIXH4Tc1DEpHq3QGjCzNvyG-srbzrQWdeBQ9SdOu61HM-K5PzzyEgH66kVL8R0nzzxRMq7-qhvcrItxp3RH7Hcw2ZCqNkoGIJFj7dzGXkRXHIagv4AeH1HUVztalSjWNeTB6e51qKhDHP5goQl-Qs2pPh69ePE_Mufy7jTtk1f_p-ElWCw",
    e: "AQAB",
  },
  {
    kty: "RSA",
    kid: "DoNsj1nLTYNSC3QI05vnd_bgfyzCYSZl2CjUkivtKEQ",
    use: "sig",
    alg: "RS256",
    n: "sbbzw5cG_yvyL3s72pJUIa32ZsxjvH5poWzRad-_jvNJrCIcO5_RBWDM12zQe_2MUpmPcjXqYYfRNRkGmBTl911myDN7HXFXf_exzod-PgArbSdCROgdVjqAEninvt8Haf8s-yE9fnaaMANWM2jbVIYfWZJ3cR08G9tDRGVCDU7oCtEdngmLn1jmYXKaCYPPiHRKs6MpHvRSzfqkir_NX3xQB-3amCOWEP4NRL52XhH4PliM1pMZVs6UAgPfquK-tS4hNiJHgk7VN8cqUK87hFsdYSN3UfVYgRMaHr40b-LiR2VVlDccwdwcP5dKB16Cw1k9SL6fpwJf7sOcuEeQ1Q",
    e: "AQAB",
  },
  {
    kty: "RSA",
    kid: "hsnAofk8H8v_nxbE0EEP3SmDMZgXYD_ChwRNKrkTznY",
    use: "sig",
    alg: "RS256",
    n: "kcF9Fa6BHBuWP3-eCGvm9ULZCE-IZTelewCEB51UudFkBypiV7EH2CvFrBZO4APS_7k7D0uX25rSTh0dz6kdUa2bvBOerdGPr0lYVEHB4BnroSOtySTsBjo8I3gWJ8oJwt-Ky7UFmEjO8QelAo7CrgFvLcSqQwuG9axBk6Wp09Y_7LvWf4f6yIMUKkEGdHW8d7juV4x3a9fQI3AK4JdfTij00tURWwU4KzIs-DXcxPJiuYqx9XlgbRHkGuW0KSbO2Y4F-UqIgfGrwfqj5ctCn7jfPHEFJpmNJb9Sjji32DDWy7XsY-d2Ozu2jjFWTJLua-iLLSZSNcNt_GFS8G2Yww",
    e: "AQAB",
  },
];
