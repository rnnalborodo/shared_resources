--  bbeo_msg.adb -- productor / servidor / consumidor con mensajes y
--  canales explícitos.  El consumidor puede elegir entre consumir
--  pares o impares.
--
--  Author : MCL


--  El canal es un recurso separado, que empleamos para comunicar
--  tareas explícitamente.
with Channels;

with Colas;

--  with ADA.Text_IO;
--  use ADA.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Msg is

   --  Número de productores y consumidores
   NCons : constant Positive := 9;
   NProd : constant Positive := 4;

   type Request_Type is (Par, Impar);

   --  Un canal para transmitirnos enteros
   package Channel_Int is
      new Channels (Integer);

   --  Otro para transmitirnos peticiones
   package Channel_Req is
      new Channels (Request_Type);

   --  Una cola de canales para almacenar las peticiones
   package Colas_Chan_Int is
      new Colas (Channel_Int.Channel);
   use Colas_Chan_Int;

   --  Definición del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Canal_Dato : in out Channel_Int.Channel);
      entry Tomar (Canal_Petic : in     Channel_Req.Channel;
                   Canal_Dato : in out Channel_Int.Channel);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is

      --  Variables que implementan el buffer de 1 dato
      Hay_Dato : Boolean := False;
      Dato : Integer := 0;  --  Evita avisos del compilador

      --  Peticiones pendientes.  Dado que *siempre* aceptamos canales
      --  para  satisfacer  peticiones,  necesitamos  almacenar  estas
      --  peticiones en algún sitio.   Usamos una cola por simplicidad
      --  y flexibilidad.  Una atención en  orden de llegada es, si no
      --  se especifica  nada más, una política  adecuada.  No podemos
      --  bloquear peticiones externas en un send o un receive de paso
      --  obligatorio  desde dentro  del recurso,  porque  eso también
      --  paralizaría el recurso.
      Pend_Tomar : array (Request_Type) of Colas_Chan_Int.Cola;
      Pend_Poner : Colas_Chan_Int.Cola;


      --  Variables temporales
      Peticion : Request_Type;
      Canal_Poner : Channel_Int.Channel;
      Canal_Tomar : Channel_Int.Channel;
      Canal_Petic_Local : Channel_Req.Channel;
      Canal_Dato_Local : Channel_Int.Channel;
   begin
      for I in Request_Type loop
         Crear_Vacia (Pend_Tomar (I));
      end loop;
      Crear_Vacia (Pend_Poner);

      loop
         --  Bucle  infinito  esperando   por  una  petición,  que  es
         --  admitida accediendo al buffer externo.  Ahora las entries
         --  no  tienen  condicion de  bloqueo,  sino  que se  guarda,
         --  internamente, cada peticion.  El servidor provee un canal
         --  de comunicación sobre el que esperar y recibir el dato.
         select
            when True =>
               accept Tomar (Canal_Petic : in     Channel_Req.Channel;
                             Canal_Dato : in out Channel_Int.Channel) do
                  Canal_Petic_Local := Canal_Petic;
                  Canal_Dato_Local := Canal_Dato;
               end Tomar;
               Channel_Req.Receive (Canal_Petic_Local, Peticion);
               Insertar (Pend_Tomar (Peticion), Canal_Dato_Local);
               --  Aquí  ya ha  acabado el  Rendez-Vous, y  el proceso
               --  cliente  está esperando  por un  dato.   No debemos
               --  atender   a  éste   inmediatamente,   porque  otros
               --  encolados podrían sufrir  inanición, ya que estamos
               --  implementando una planificación.
         or
            --  Podemos poner siempre que haya sitio, y es posible que
            --  haya  alguna petición  bloqueada que  se  pueda servir
            --  ahora.
            when True =>
               accept Poner (Canal_Dato : in out Channel_Int.Channel) do
                  Insertar (Pend_Poner, Canal_Dato);
               end Poner;
         end select;

         --  Aqui  realizar  todo  el  servicio  de  poner/tomar.   La
         --  condición del bucle  es la disyunción de las  CPRE de las
         --  operaciones que pueden ser atendidas; después podemos ver
         --  cuál de ellas atendemos.

         while                          --  Precondición de Tomar
           (Hay_Dato and then not
            Es_Vacia (Pend_Tomar (Request_Type'Val (Dato mod 2))))
           or                        --  Precondición de Poner
           (not Hay_Dato and not Es_Vacia (Pend_Poner)) loop

            if not Hay_Dato and not Es_Vacia (Pend_Poner) then
               --  Esta rama atiende a los que quieren poner.
               Primero (Pend_Poner, Canal_Poner);
               Borrar (Pend_Poner);
               Channel_Int.Receive (Canal_Poner, Dato);
               Hay_Dato := True;
            else
               --  Esta rama atiende a los que quieren tomar.
               Primero (Pend_Tomar (Request_Type'Val (Dato mod 2)),
                        Canal_Tomar);
               Borrar (Pend_Tomar (Request_Type'Val (Dato mod 2)));
               Channel_Int.Send (Canal_Tomar, Dato);
               Hay_Dato := False;
            end if;
         end loop;
      end loop;
   end BufServer;

   --  Variable que representa la tarea servidora
   TheBufServer : BufServer;

   --  Definición de los productores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Productor;
   task body Productor is
      Dato : Natural := 0;
      Data_Channel : Channel_Int.Channel;
   begin
      Channel_Int.Create (Data_Channel);
      loop
         TheBufServer.Poner (Data_Channel);
         Channel_Int.Send (Data_Channel, Dato);
         Put_Line ("Productor envió " & Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
      end loop;
   end Productor;

   --  Definición de los consumidores; mandan mensajes directamente a
   --  la tarea que implementa el servidor
   task type Consumidor (Which_Type : Request_Type);
   task body Consumidor is
      Dato : Natural;
      Data_Channel : Channel_Int.Channel;
      Req_Channel : Channel_Req.Channel;
   begin
      Channel_Int.Create (Data_Channel);
      Channel_Req.Create (Req_Channel);
      loop
         --  Pedimos que nos manden el dato, y decimos por qué
         --  canal lo vamos a esperar
         TheBufServer.Tomar (Req_Channel, Data_Channel);
         Channel_Req.Send (Req_Channel, Which_Type);
         Channel_Int.Receive (Data_Channel, Dato);
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
end Bb_Eo_Msg;
