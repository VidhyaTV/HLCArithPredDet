import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedWriter;
import java.io.File;
import java.util.Vector;
import java.util.Deque;
import java.util.ArrayDeque;
class Process
{
    int id;
    int prev_pt;
    int lastsendorrecorlocevntpt;//variable to check if multiple events -msg send/rcv or local event happened at the same instant --used to update prev(Old) pt,l,c only when the first event occurs at a specific physical time

    Clock clock=new Clock();
    Clock prev_clock=new Clock();
    //queue to remember interval-candidates
    Deque<Candidate> candQueue;
    //queue to remember values corresponding to message sends
    Deque<MessageSendStruct> log;
    int msg_counter;

    Deque<ChangePoint> cPointQueue;

    Process(int unique_id, Clock nwclock)
    {
        id=unique_id;
        clock=nwclock;

        msg_counter=0;
        if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
        {
            Vector<Integer> hlcvector=new Vector<Integer>();
            hlcvector.add(0);
            hlcvector.add(0);
            hlcvector.add(0);
            prev_clock= new HLC(hlcvector);
        }
        prev_pt=0;
        log = new ArrayDeque<MessageSendStruct>();
        candQueue= new ArrayDeque<Candidate>();
        cPointQueue= new ArrayDeque<ChangePoint>();
        lastsendorrecorlocevntpt=-1;
    }

    void setId(int passed_id){id=passed_id;}
    void setProcClock(Clock nwclock){clock.setClock(nwclock.getClock());}
    void setProcOldClock(Clock passed_clock){prev_clock.setClock(passed_clock.getClock());}
    void setlastsendorrecorlocevntpt(int sendreclocventpt){lastsendorrecorlocevntpt=sendreclocventpt;}

    int getId(){return id;}
    Clock getProcClock(){return clock;}
    Clock getProcOldClock(){return prev_clock;}

    int getlastsendorrecorlocevntpt(){return lastsendorrecorlocevntpt;}

    Deque<Candidate> getCandQueue()
    {
        return candQueue;
    }

    void setCandQueue(Deque<Candidate> updatedQueue)
    {
        candQueue=updatedQueue;
    }
    Deque<ChangePoint> getCPtQueue()
    {
        return cPointQueue;
    }

    void setCPtQueue(Deque<ChangePoint> updatedQueue)
    {
        cPointQueue=updatedQueue;
    }

    //clear queue method at a process - given time x --CLEARQUEUE
    Candidate clearQueueTill(Clock tillend)
    {
        //System.out.println("clear queue at process"+id+"tillendl"+tillendl+"tillendc"+tillendc);
        while(!(candQueue.isEmpty()) &&(((candQueue.peekFirst()).getEndClock().lessThan(tillend)) || ((candQueue.peekFirst()).getEndClock().equalTo(tillend))))
        {
            //pop all candidates with start time smaller than x
            candQueue.removeFirst();
        }
        //set the front candidate in my queue as my representative in Token--will be done at the method that called this method
        return candQueue.peekFirst();
    }

    Candidate newCandidateOccurance(Clock intervalstart, Clock intervalend)
    {
        Candidate newCand= new Candidate(intervalstart, intervalend);
        candQueue.add(newCand);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter candbw2= new BufferedWriter(new FileWriter("Candidates"+id+".txt", true));//true for append
                candbw2.append("<"+intervalstart.getClock()+"> to <"+intervalend.getClock()+">\n");
                candbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
        return newCand;
    }
    void newChangePoint(Clock cPtTime, int endPtIdentifier, int value)
    {
        ChangePoint newCPt= new ChangePoint(cPtTime, endPtIdentifier, value);
        cPointQueue.add(newCPt);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter cptbw2= new BufferedWriter(new FileWriter("ChangePoints"+id+".txt", true));//true for append
                cptbw2.append("<"+cPtTime.getClock()+", type: "+endPtIdentifier+", value"+value+">\n");
                cptbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
    }
    void updateClockLocalOrSengMsg(int physicalTime, boolean sendmsg)
    {
        if(lastsendorrecorlocevntpt!=physicalTime)//if a message send/receive did not happen at the same instant update old pt - otherwise don't because old pt is required for interval reporting
        {//pt is also same-still update old_value
            setProcOldClock(getProcClock());
        }
        clock.updateLocal(physicalTime);

        //System.out.println("At Process:"+id+"; Physical Time:"+physicalTime);

        if(sendmsg)
        {
            Clock formsgclk=new Clock();
            //push message id, l, c into queue
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
            {
                Vector<Integer> hlcvector=new Vector<Integer>();
                hlcvector.add(0);
                hlcvector.add(0);
                hlcvector.add(0);
                formsgclk=new HLC(hlcvector);
            }
            formsgclk.setClock(clock.getClock());//copying clock values to new clk object for msg timestamping
            MessageSendStruct newmsg= new MessageSendStruct(msg_counter++,formsgclk);
            log.add(newmsg);
        }

        setlastsendorrecorlocevntpt(physicalTime);
    }
    void updateClockMessageRceive(int receiver_time, Clock sndrClk)
    {
        if(getlastsendorrecorlocevntpt()!=receiver_time)
        {
            setProcOldClock(getProcClock());

        }
        clock.updateMsgRcv(receiver_time,sndrClk);

        setlastsendorrecorlocevntpt(receiver_time);
    }
    MessageSendStruct getClockfromQueue(int passed_phytime)
    {
        while(log.peek().getMsgClock().getClock().get(0)!=passed_phytime)
        {
            //System.out.println(passed_phytime+","+log.peek().getPt());
            System.out.println("FIFO VIOLATED...popping..");
            log.removeFirst();
        }
        MessageSendStruct msgptclk=log.peek();
        if(msgptclk!=null)
        {
            if(passed_phytime == msgptclk.getMsgClock().getClock().get(0))
            {
                //System.out.println("FOUND MATCHING SEND");
                return log.removeFirst();
            }
            else
            {
                System.out.println("CODE THAT SHOULD NOT EXECUTE");
                System.exit(0);
            }
            return log.peek();
        }
        else
        {
            System.out.println("SEND QUEUE EMPTY");
            System.exit(0);
            return msgptclk;
        }
    }

    void printCandQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in write mode so anything already existing will be cleared
            }

            if (!candQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (Candidate cand : candQueue)
                {
                    bw_deb1.write("<"+cand.getStartClock().getClock().get(1)+","+cand.getStartClock().getClock().get(2)+">-<" + cand.getEndClock().getClock().get(1)+","+ cand.getEndClock().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }
    void printCPtQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in append mode so anything already existing will not be cleared
            }
            if (!cPointQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (ChangePoint cPt : cPointQueue)
                {
                    bw_deb1.write("<" + cPt.getcPointTimestamp().getClock().get(1)+"," + cPt.getcPointTimestamp().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }

    Deque<ChangePoint> cleanUpChangePtQ(){
        Deque<ChangePoint> cleansedQ = new ArrayDeque<ChangePoint>();
        if (!cPointQueue.isEmpty())//if there is at least one unprocessed changepoint
        {
            Deque<ChangePoint> intermediateCPtsQ = new ArrayDeque<ChangePoint>();
            ChangePoint currentLCPt = getCPtQueue().removeFirst(); //Lj
            ChangePoint currentRCPt = getCPtQueue().removeFirst(); //Rj
            if (cPointQueue.peek() == null) {//queue has changepoints of a single interval
                cPointQueue.add(currentLCPt);
                cPointQueue.add(currentRCPt);
                return cPointQueue;
            }
            while (cPointQueue.peek() != null) {
                ChangePoint nextLCPt = getCPtQueue().removeFirst(); //Li
                ChangePoint nextRCPt = getCPtQueue().removeFirst(); //Ri
                //no overlap
                if (currentRCPt.getcPointTimestamp().lessThan(nextLCPt.getcPointTimestamp()) || currentRCPt.getcPointTimestamp().equalTo(nextLCPt.getcPointTimestamp())) {
                    //clean up
                    //put current interval
                    cleansedQ.add(currentLCPt);
                    cleansedQ.add(currentRCPt);
                    while (intermediateCPtsQ.peek() != null) {//process any intermediate changepoints
                        //change L's timestamp of every entry in intermediateCPtsQ to Rj's timestamp
                        ChangePoint intermediateCPtL = intermediateCPtsQ.removeFirst(); //processing from last intermediate interval so that they can be added to the queue front in reverse order
                        ChangePoint intermediateCPtR = intermediateCPtsQ.removeFirst();
                        //currentCPt overlapped with entire intermediate interval drop it else modify its left end
                        if (intermediateCPtR.getcPointTimestamp().lessThan(currentRCPt.getcPointTimestamp()) || intermediateCPtR.getcPointTimestamp().equalTo(currentRCPt.getcPointTimestamp())) {
                            continue;//ignore any intermediate intervals with smaller value
                        }
                        //set L value to Rj value
                        Clock currRClock = currentRCPt.getcPointTimestamp();
                        Clock origLTime = intermediateCPtL.getcPointTimestamp();
                        origLTime.setClock(currRClock.getClock());
                        intermediateCPtL.setcPointTimestamp(origLTime);
                        //put it back in the original queue
                        //in the right order
                        cleansedQ.add(intermediateCPtL);
                        cleansedQ.add(intermediateCPtR);
                        // remember the right endpoint of the current intermediate interval to be used as left endpoint of the next intermediate interval if needed
                        currentRCPt = intermediateCPtR;
                    }
                    currentLCPt = nextLCPt;
                    currentRCPt = nextRCPt;
                } else if (nextLCPt.getiValue() > currentLCPt.getiValue()) {//there is overlap and the successive overlapping interval has higher value
                    //discard intermediateCPtsQ
                    intermediateCPtsQ.clear();
                    //set Rj's timestamp to Li's timestamp
                    Clock nextLClock = nextLCPt.getcPointTimestamp();
                    Clock origRTime = currentRCPt.getcPointTimestamp();
                    origRTime.setClock(nextLClock.getClock());
                    currentRCPt.setcPointTimestamp(origRTime);
                    if (!currentRCPt.getcPointTimestamp().lessThan(currentLCPt.getcPointTimestamp())) {
                        cleansedQ.add(currentLCPt);
                        cleansedQ.add(currentRCPt);
                    }
                    currentLCPt = nextLCPt;
                    currentRCPt = nextRCPt;
                } else {//there is overlap and the successive overlapping interval has smaller value
                    //set Li's timestamp to Rj's timestamp
                    Clock currRClock = currentRCPt.getcPointTimestamp();
                    Clock origLTime = nextLCPt.getcPointTimestamp();
                    origLTime.setClock(currRClock.getClock());
                    nextLCPt.setcPointTimestamp(origLTime);
                    intermediateCPtsQ.add(nextLCPt);
                    intermediateCPtsQ.add(nextRCPt);
                    //currentLCPt and currentRCPt say the same
                }
            }//end of while(cPointQueue.peek() != null)
        }//end of if(!cPointQueue.isEmpty())
        return cleansedQ;
    }
}