--  bbeo_rv.adb --  productor / servidor / consumidor con Rendez-Vous puro.
--  El consumidor puede elegir entre consumir pares o impares.
--
--  Author : MCL

--  with ADA.Text_IO;
--  use ADA.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Rv is

   --  Número de productores y consumidores
   NCons : constant Positive := 9;
   NProd : constant Positive := 4;

   type Request_Type is (Par, Impar);

   --  Definición del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Item : in Integer);
      entry Tomar_Par (Item : out Integer);
      entry Tomar_Impar (Item : out Integer);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is
      --  Variables que implementan el buffer de 1 dato
      Hay_Dato : Boolean := False;
      Dato : Integer := 0;  --  Avoid compiler warnings
   begin
      loop
         --  Bucle  infinito  esperando   por  una  petición,  que  es
         --  admitida  accediendo  al   buffer  externo.   Para  poder
         --  referirnos únicamente al estado, desdoblamos la operación
         --  Tomar  en dos.   Ello permite  proyectar  la precondición
         --  sobre los argumentos de entrada de los que depende.
         select
            when Hay_Dato and then Dato mod 2 = 0 =>
               accept Tomar_Par (Item : out Integer)
               do
                  Item := Dato;
                  Hay_Dato := False;
               end Tomar_Par;
         or
            when Hay_Dato and then Dato mod 2 = 1 =>
               accept Tomar_Impar (Item : out Integer)
               do
                  Item := Dato;
                  Hay_Dato := False;
               end Tomar_Impar;
         or
 --  Podemos poner siempre que haya sitio, y es posible que
 --  haya alguna petición bloqueada que se pueda servir ahora.
            when not Hay_Dato =>
               accept Poner (Item : in Integer) do
                  Hay_Dato := True;
                  Dato := Item;
               end Poner;

         end select;
      end loop;
   end BufServer;

   procedure Tomar (Server : in out BufServer;
                    Req : in     Request_Type;
                    Dato : out Integer) is
   begin
      if Req = Par then
         Server.Tomar_Par (Dato);
      else
         Server.Tomar_Impar (Dato);
      end if;
   end Tomar;

   procedure Poner (Server : in out BufServer;
                    Dato : in     Integer) is
   begin
      Server.Poner (Dato);
   end Poner;

   --  Variable que representa la tarea servidora
   TheBufServer : BufServer;

   --  Definición de los productores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Productor;
   task body Productor is
      Dato : Natural := 0;
   begin
      loop
         Poner (TheBufServer, Dato);
         Put_Line ("Productor envió " & Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
      end loop;
   end Productor;


   --  Definición de los consumidores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Consumidor (Which_Type : Request_Type);
   task body Consumidor is
      Dato : Natural;
   begin
      loop
         --  Pedimos que nos manden el dato, y decimos por qué
         --  canal lo vamos a esperar
         Tomar (TheBufServer, Which_Type, Dato);
         Put_Line ("Consumidor obtuvo " & Integer'Image (Dato));
         delay 0.5;
      end loop;
   end Consumidor;


   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheEvenConsumers : array (1 .. NCons / 2) of Consumidor (Par);
   TheOddConsumers : array (1 .. NCons / 2) of Consumidor (Impar);

begin --  Principal
   null;
end Bb_Eo_Rv;
