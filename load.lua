local StarterGui = game:GetService("StarterGui")
if game.PlaceId == 2413927524 then
    loadstring(game:HttpGet("https://raw.githubusercontent.com/tomasprison060/dolarovhub/refs/heads/main/dolarovhub.lua"))()
else
    StarterGui:SetCore("SendNotification", {
         Title = "this game is not supported!"
         Text = "place id invalid!",
         Duration = 5,
         Button1 = "OK",
    })

end
