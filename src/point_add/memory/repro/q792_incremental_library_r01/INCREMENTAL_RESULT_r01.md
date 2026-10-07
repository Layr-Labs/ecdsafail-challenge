# Aktualizacje przyrostowe predykatów — wynik iteracji

GPT-6 Astra, 2026-09-13. Baza: oficjalnie poprawny Q792 / T910 644 642, zamrożony `q792-library-release-20260913.tkt_202l/stage-r01-workspace`.

Zaimplementowany prototyp optymalizatora zmniejszył koszt czterech pełnych szablonów przejścia z **721 894 do 711 372 Toffoli**: **10 522 mniej, czyli 1,4576%**. Liczba wszystkich operacji spadła z **1 266 478 do 1 262 144**. Zamienniki korzystają wyłącznie z przewodów istniejących we fragmencie. Każdy etap ma dokładny dowód symboliczny CPU oraz ocenę rzeczywistych obwodów na obu Intel Arc Pro B50, po 43 008 przypadków bez błędów.

**To wynik czterech szablonów w trybie pełnego zakresu, a nie nowy licznik całego obwodu Q792.** Zysk dla wszystkich 808 szablonów harmonogramu i całego punktowego dodawania pozostaje niezmierzony. Nie zintegrowano tej iteracji z wydanym źródłem, nie wykonano nowej kwalifikacji 9024 ani nowego submitu. Cel radykalnej redukcji, w szczególności 20%, nie został osiągnięty. Kolejne osiem przebiegów par nie osiągnęło punktu stałego; ostatni nadal oszczędzał 118 T.

## Pierwszy pomiar kosztu powtórzeń

Audyt dotyczy tych samych fizycznych sterowań i celu CCX, z uwzględnieniem zmian ich wartości pomiędzy wystąpieniami. Przeszukano najbliższą równą parę wśród ośmiu ostatnich zapisów CCX danego celu, do odległości 8192 operacji.

- 577 050 par o powtarzających się numerach sterowań i celu.
- 703 040 różnych bramek Toffoli jest końcem co najmniej jednej takiej pary. Każdą bramkę liczono raz; pary mogą się nakładać.
- Maksymalny zbiór par o rozłącznych przedziałach obejmuje **193 196 T**, czyli 26,76% kosztu czterech szablonów. To koszt punktów końcowych, bez kosztu wnętrz przedziałów.
- 431 768 par ma pomiędzy obliczeniami odczyt akumulatora. Nie można usuwać jego wcześniejszego zapisu bez skorygowania skutków tych odczytów.

Te liczby opisują wystąpienia, nie dowodzą zbędności bramek. Dokładny zysk po uwzględnieniu kolizji i wszystkich odtworzeń wynosi podane wyżej 10 522 T. Nie mnożono wyniku czterech szablonów przez liczbę bloków.

## Co robi optymalizator

Pierwsza wersja szuka par `p ^= f; D; p ^= g`, dla których D nie odczytuje p. Zachowuje D i wylicza dokładnie:

`delta(y) = f(D^-1(y)) XOR g(y)`.

Współrzędne zmieniają się po każdej bramce, również Toffolim. Reprezentacja ANF redukuje jednomiany z uwzględnieniem `x*x=x` i parzystości współczynników. Nie zakłada zerowych kubitów ani osiągalności specjalnych stanów. GPU oblicza koszt części kwadratowej; CPU niezależnie sprawdza rangę, syntezę, wszystkie wyjścia i odtworzenie sterowań.

Pierwszy przebieg: 215 094 pary, 199 108 dokładnych różnic, 28 891 ocenionych na GPU różnic kwadratowych, 8570 dodatnich zamienników z dowodem. Wybór przedziałów daje 2552 zamiany / 3710 T mniej. Osiem kolejnych przebiegów na zmienionych wejściach daje dalsze 2613 T mniej. Nie powtarzano pomiarów niezmienionego kandydata.

Osobna wersja scala serie co najmniej trzech zapisów do jednego akumulatora. Znalazła 138 dodatnich zamienników, z których 63 rozłączne oszczędzają 409 T. Jest to wariant alternatywny względem pierwszej wersji: **jego wyniku nie dodawano do wyniku łącznego**.

Rozszerzenie wektorowe dopuszcza odczyty p. Przechowuje różnicę całego stanu `e`, tak aby stan po pominięciu pierwszej bramki wraz z korektą odtwarzał stan oryginalny. Przejście przez `CCX(a,b,t)` wnosi do korekty celu:

`a*e_b XOR b*e_a XOR e_a*e_b`.

Następnie wszystkie składowe przelicza się do współrzędnych po tej bramce. Końcowy predykat scala się z całym wektorem korekty. Synteza zachowuje wszystkie wyjścia, także przewody, które odczytywały predykat.

Na bazowych szablonach: 415 791 par z odczytami, 360 734 dokładne wektory, 3074 ocenione funkcje kwadratowe, 3002 dodatnie dowody; 2516 rozłącznych zamian daje 4019 T mniej. Tego wyniku również nie sumowano z alternatywnym przebiegiem na tej samej bazie. **Ponowne wyszukiwanie na wyniku dziewięciu przebiegów skalarnych dało 4199 dodatkowych T mniej**. Stąd wspólny wynik: 3710 + 2613 + 4199 = 10 522.

## Biblioteka i dowody

Biblioteka zawiera **74 różne funkcje aktualizacji**: 70 z jednym Toffolim, trzy afiniczne i identyczność. Klucz obejmuje znormalizowaną pełną funkcję, role zmienianych wyjść i kontrakt `TRUE`. Nie jest oparty wyłącznie na zapisie sekwencji. Przechowywane są pochodzenie, zamiennik i dowody. Nie są to 74 nowe redukcje całego obwodu.

Każda funkcja obejmuje najwyżej 10 przewodów. CPU sprawdził całą tablicę prawdy i odwrotność, a obie B50 niezależnie wykonały wszystkie jej wejścia w bankach rozłącznych funkcji: 4096 przypadków, zero błędów. SHA256 biblioteki: `11ebd7bd9c41ef03ee6a8f7e6ccb15ac79fdefe39392f811603964f1f0f43f6b`.

Niezależny test wzoru skalarnego: przykład użytkownika 16/16, następnie 512 programów / 50 640 pełnych stanów. Wersja wektorowa: 1024 programy / 38 208 stanów, w tym 854 programy odczytujące początkowy cel; porównanie bezpośredniej symulacji, całego stanu i odwrotności PASS. Testy te uzupełniają dokładny dowód algebraiczny każdego wybranego zamiennika.

## Dlaczego nie ma dużego cięcia

W 170 217 z 199 108 dokładnych różnic skalarnych stopień ANF przekracza dwa. Dalsze 20 321 ma część kwadratową wymagającą co najmniej dwóch niezależnych iloczynów. Przy zachowanym wnętrzu D i dowolnych wejściach takie korekty nie mają realizacji za pomocą najwyżej jednego Toffoliego i dowolnej liczby X/CNOT. Jedna bramka Toffoli otoczona bramkami afinicznymi tworzy najwyżej jedną kwadratową funkcję iloczynową.

To lokalne ograniczenie konkretnej klasy zamian **dwóch punktów końcowych**, nie dolna granica kosztu całego obwodu. Nie wyklucza zmiany wnętrza D, większej wspólnej syntezy ani użycia udowodnionych kontraktów między blokami. O wartości pamięci decyduje koszt aktualizacji przechowywanej funkcji i skutków jej odczytów, nie sama częstość ponownego wystąpienia CCX.

## Pliki i status

- `incremental-r20/census.json`, `result.json`: pierwszy przebieg par.
- `incremental-r21/result.json`: alternatywne serie zapisów.
- `incremental-loop-r22/result.json`: osiem dalszych przebiegów.
- `incremental-vector-r24/result.json`: wektory na oryginalnej bazie.
- `incremental-vector-after-loop-r25/combined-result.json`: wiążący wynik łączny.
- `incremental-proof-r23/`, `incremental-vector-proof-r26/`: niezależne testy lematu.
- `incremental-library-r27/proved-library.json`: biblioteka z kompletnymi dowodami CPU/GPU.
- `incremental-metrics-r28/result.json`: audyt kosztu powtórzeń. Prostuje również pomocnicze etykiety `same_control_pairs` i `nonlinear_input_update_pairs` w r24/r25, odziedziczone jako stałe z szablonu skryptu. Ta korekta metadanych nie zmienia zamienników, T/N, dowodów ani wyników GPU.

Wcześniejszy submit `48e108c1-f909-43f2-b8d1-3279ee2b026c` uzyskał oficjalny correctness PASS: Q792 / T910 644 642. Odczyt 11:37:44 UTC po wymaganych 50 minutach. Serwis odrzucił go wyłącznie jako `score did not improve current best`; nie jest to status accepted. Brak kolejnego submitu, oczekujących odczytów, aktywnych testów, agentów i monitorów.
